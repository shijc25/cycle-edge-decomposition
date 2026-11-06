import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch170
import Cycle12.MergedCutProfiles.Batch171
import Cycle12.MergedCutProfiles.Batch172

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch085

def retention1020 : RatCutRetentionCertificate := ⟨(13/250),(209/4000),(1229297760687617297/2463513668583235519),(532492841882012443/62500000000000000),(21/20),(211671136586847638412827175605428003839/212997136752804977200000000000000000000),false,MergedCutProfiles.Batch170.profile6822,(fun _ => MergedCutProfiles.Batch170.profile6822)⟩
theorem profilesValid1020 : retention1020.ProfilesValid := by
  exact MergedCutProfiles.Batch170.valid6822
theorem numericValid1020 : retention1020.NumericValid := by decide +kernel
def certificate1020 : RatCutBinCertificate := ⟨⟨retention1020,(319993243018783229/125000000000000000),(132328855686888103/1000000000000000000),(3444023630450536769/250000000000000000),(475816539608415039/2000000000000000),(120994176988991331/125000000000000000)⟩,(990634636477481583/1000000000000000000),(83206976256476987/200000000000000000),(109553729023996197/500000000000000000),(90656721960017547/500000000000000000)⟩
theorem valid1020 : certificate1020.Valid := by decide +kernel
theorem sound1020 : certificate1020.Sound := rat_cut_bin_certificate_sound certificate1020 profilesValid1020 numericValid1020 valid1020

def retention1021 : RatCutRetentionCertificate := ⟨(13/250),(209/4000),(1/2),(8605084324813321079/1000000000000000000),(21/20),(13659100162376356639022366305553114060039/13768134919701313726400000000000000000000),false,MergedCutProfiles.Batch170.profile6819,(fun _ => MergedCutProfiles.Batch170.profile6819)⟩
theorem profilesValid1021 : retention1021.ProfilesValid := by
  exact MergedCutProfiles.Batch170.valid6819
theorem numericValid1021 : retention1021.NumericValid := by decide +kernel
def certificate1021 : RatCutBinCertificate := ⟨⟨retention1021,(319993243018783229/125000000000000000),(132328855686888103/1000000000000000000),(3444023630450536769/250000000000000000),(475816539608415039/2000000000000000),(966259512714821081/1000000000000000000)⟩,(990634636477481583/1000000000000000000),(52095526509275801/125000000000000000),(21846850233031757/100000000000000000),(451663648320597/2500000000000000)⟩
theorem valid1021 : certificate1021.Valid := by decide +kernel
theorem sound1021 : certificate1021.Sound := rat_cut_bin_certificate_sound certificate1021 profilesValid1021 numericValid1021 valid1021

def retention1022 : RatCutRetentionCertificate := ⟨(209/4000),(21/400),(948502854311281189/17055936265939102859),(850165604452536769/1000000000000000000),(57/20),(2605665189004190311561/1280000000000000000000),true,MergedCutProfiles.Batch170.profile6823,![MergedCutProfiles.Batch170.profile6823,MergedCutProfiles.Batch170.profile6824,MergedCutProfiles.Batch170.profile6825,MergedCutProfiles.Batch170.profile6826,MergedCutProfiles.Batch170.profile6827,MergedCutProfiles.Batch170.profile6828,MergedCutProfiles.Batch170.profile6829,MergedCutProfiles.Batch170.profile6830,MergedCutProfiles.Batch170.profile6831,MergedCutProfiles.Batch170.profile6832,MergedCutProfiles.Batch170.profile6833,MergedCutProfiles.Batch170.profile6834,MergedCutProfiles.Batch170.profile6835,MergedCutProfiles.Batch170.profile6836,MergedCutProfiles.Batch170.profile6837,MergedCutProfiles.Batch170.profile6838]⟩
theorem profilesValid1022 : retention1022.ProfilesValid := by
  change ∀ j : Fin 16, (retention1022.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch170.valid6823
  · exact MergedCutProfiles.Batch170.valid6824
  · exact MergedCutProfiles.Batch170.valid6825
  · exact MergedCutProfiles.Batch170.valid6826
  · exact MergedCutProfiles.Batch170.valid6827
  · exact MergedCutProfiles.Batch170.valid6828
  · exact MergedCutProfiles.Batch170.valid6829
  · exact MergedCutProfiles.Batch170.valid6830
  · exact MergedCutProfiles.Batch170.valid6831
  · exact MergedCutProfiles.Batch170.valid6832
  · exact MergedCutProfiles.Batch170.valid6833
  · exact MergedCutProfiles.Batch170.valid6834
  · exact MergedCutProfiles.Batch170.valid6835
  · exact MergedCutProfiles.Batch170.valid6836
  · exact MergedCutProfiles.Batch170.valid6837
  · exact MergedCutProfiles.Batch170.valid6838
theorem numericValid1022 : retention1022.NumericValid := by decide +kernel
def certificate1022 : RatCutBinCertificate := ⟨⟨retention1022,(1102754281042186467/500000000000000000),(26755931122933953/200000000000000000),(34586963781175297/2500000000000000),(59077136701526038033/250000000000000000),(1974880250153637631/1000000000000000000)⟩,(495945778655119639/500000000000000000),(367745670546960509/1000000000000000000),(132185708782697493/500000000000000000),(141079763679955457/1000000000000000000)⟩
theorem valid1022 : certificate1022.Valid := by decide +kernel
theorem sound1022 : certificate1022.Sound := rat_cut_bin_certificate_sound certificate1022 profilesValid1022 numericValid1022 valid1022

def retention1023 : RatCutRetentionCertificate := ⟨(209/4000),(21/400),(1639510491685564584/17055936265939102859),(948502854311281189/1000000000000000000),(13/5),(2447816852141654085337/1280000000000000000000),true,MergedCutProfiles.Batch170.profile6839,![MergedCutProfiles.Batch170.profile6839,MergedCutProfiles.Batch171.profile6840,MergedCutProfiles.Batch171.profile6841,MergedCutProfiles.Batch171.profile6842,MergedCutProfiles.Batch171.profile6843,MergedCutProfiles.Batch171.profile6844,MergedCutProfiles.Batch171.profile6845,MergedCutProfiles.Batch171.profile6846,MergedCutProfiles.Batch171.profile6847,MergedCutProfiles.Batch171.profile6848,MergedCutProfiles.Batch171.profile6849,MergedCutProfiles.Batch171.profile6850,MergedCutProfiles.Batch171.profile6851,MergedCutProfiles.Batch171.profile6852,MergedCutProfiles.Batch171.profile6853,MergedCutProfiles.Batch171.profile6854]⟩
theorem profilesValid1023 : retention1023.ProfilesValid := by
  change ∀ j : Fin 16, (retention1023.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch170.valid6839
  · exact MergedCutProfiles.Batch171.valid6840
  · exact MergedCutProfiles.Batch171.valid6841
  · exact MergedCutProfiles.Batch171.valid6842
  · exact MergedCutProfiles.Batch171.valid6843
  · exact MergedCutProfiles.Batch171.valid6844
  · exact MergedCutProfiles.Batch171.valid6845
  · exact MergedCutProfiles.Batch171.valid6846
  · exact MergedCutProfiles.Batch171.valid6847
  · exact MergedCutProfiles.Batch171.valid6848
  · exact MergedCutProfiles.Batch171.valid6849
  · exact MergedCutProfiles.Batch171.valid6850
  · exact MergedCutProfiles.Batch171.valid6851
  · exact MergedCutProfiles.Batch171.valid6852
  · exact MergedCutProfiles.Batch171.valid6853
  · exact MergedCutProfiles.Batch171.valid6854
theorem numericValid1023 : retention1023.NumericValid := by decide +kernel
def certificate1023 : RatCutBinCertificate := ⟨⟨retention1023,(1102754281042186467/500000000000000000),(26755931122933953/200000000000000000),(34586963781175297/2500000000000000),(59077136701526038033/250000000000000000),(1856894417869352787/1000000000000000000)⟩,(495945778655119639/500000000000000000),(5854932782757057/15625000000000000),(257465136534707597/1000000000000000000),(141215154629273157/1000000000000000000)⟩
theorem valid1023 : certificate1023.Valid := by decide +kernel
theorem sound1023 : certificate1023.Sound := rat_cut_bin_certificate_sound certificate1023 profilesValid1023 numericValid1023 valid1023

def retention1024 : RatCutRetentionCertificate := ⟨(209/4000),(21/400),(4707386105717260942/17055936265939102859),(204938811460695573/125000000000000000),(17/10),(233192907113662642203/160000000000000000000),true,MergedCutProfiles.Batch171.profile6855,![MergedCutProfiles.Batch171.profile6855,MergedCutProfiles.Batch171.profile6856,MergedCutProfiles.Batch171.profile6857,MergedCutProfiles.Batch171.profile6858,MergedCutProfiles.Batch171.profile6859,MergedCutProfiles.Batch171.profile6860,MergedCutProfiles.Batch171.profile6861,MergedCutProfiles.Batch171.profile6862,MergedCutProfiles.Batch171.profile6863,MergedCutProfiles.Batch171.profile6864,MergedCutProfiles.Batch171.profile6865,MergedCutProfiles.Batch171.profile6866,MergedCutProfiles.Batch171.profile6867,MergedCutProfiles.Batch171.profile6868,MergedCutProfiles.Batch171.profile6869,MergedCutProfiles.Batch171.profile6870]⟩
theorem profilesValid1024 : retention1024.ProfilesValid := by
  change ∀ j : Fin 16, (retention1024.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch171.valid6855
  · exact MergedCutProfiles.Batch171.valid6856
  · exact MergedCutProfiles.Batch171.valid6857
  · exact MergedCutProfiles.Batch171.valid6858
  · exact MergedCutProfiles.Batch171.valid6859
  · exact MergedCutProfiles.Batch171.valid6860
  · exact MergedCutProfiles.Batch171.valid6861
  · exact MergedCutProfiles.Batch171.valid6862
  · exact MergedCutProfiles.Batch171.valid6863
  · exact MergedCutProfiles.Batch171.valid6864
  · exact MergedCutProfiles.Batch171.valid6865
  · exact MergedCutProfiles.Batch171.valid6866
  · exact MergedCutProfiles.Batch171.valid6867
  · exact MergedCutProfiles.Batch171.valid6868
  · exact MergedCutProfiles.Batch171.valid6869
  · exact MergedCutProfiles.Batch171.valid6870
theorem numericValid1024 : retention1024.NumericValid := by decide +kernel
def certificate1024 : RatCutBinCertificate := ⟨⟨retention1024,(1102754281042186467/500000000000000000),(26755931122933953/200000000000000000),(34586963781175297/2500000000000000),(59077136701526038033/250000000000000000),(1421192687280649331/1000000000000000000)⟩,(495945778655119639/500000000000000000),(51441636896076687/125000000000000000),(27884973003518313/125000000000000000),(71055021870635803/500000000000000000)⟩
theorem valid1024 : certificate1024.Valid := by decide +kernel
theorem sound1024 : certificate1024.Sound := rat_cut_bin_certificate_sound certificate1024 profilesValid1024 numericValid1024 valid1024

def retention1025 : RatCutRetentionCertificate := ⟨(209/4000),(21/400),(7741916987168355334/17055936265939102859),(2353693052858630471/500000000000000000),1,(133659025961736389591/128000000000000000000),true,MergedCutProfiles.Batch171.profile6871,![MergedCutProfiles.Batch171.profile6871,MergedCutProfiles.Batch171.profile6872,MergedCutProfiles.Batch171.profile6873,MergedCutProfiles.Batch171.profile6874,MergedCutProfiles.Batch171.profile6875,MergedCutProfiles.Batch171.profile6876,MergedCutProfiles.Batch171.profile6877,MergedCutProfiles.Batch171.profile6878,MergedCutProfiles.Batch171.profile6879,MergedCutProfiles.Batch172.profile6880,MergedCutProfiles.Batch172.profile6881,MergedCutProfiles.Batch172.profile6882,MergedCutProfiles.Batch172.profile6883,MergedCutProfiles.Batch172.profile6884,MergedCutProfiles.Batch172.profile6885,MergedCutProfiles.Batch172.profile6886]⟩
theorem profilesValid1025 : retention1025.ProfilesValid := by
  change ∀ j : Fin 16, (retention1025.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch171.valid6871
  · exact MergedCutProfiles.Batch171.valid6872
  · exact MergedCutProfiles.Batch171.valid6873
  · exact MergedCutProfiles.Batch171.valid6874
  · exact MergedCutProfiles.Batch171.valid6875
  · exact MergedCutProfiles.Batch171.valid6876
  · exact MergedCutProfiles.Batch171.valid6877
  · exact MergedCutProfiles.Batch171.valid6878
  · exact MergedCutProfiles.Batch171.valid6879
  · exact MergedCutProfiles.Batch172.valid6880
  · exact MergedCutProfiles.Batch172.valid6881
  · exact MergedCutProfiles.Batch172.valid6882
  · exact MergedCutProfiles.Batch172.valid6883
  · exact MergedCutProfiles.Batch172.valid6884
  · exact MergedCutProfiles.Batch172.valid6885
  · exact MergedCutProfiles.Batch172.valid6886
theorem numericValid1025 : retention1025.NumericValid := by decide +kernel
def certificate1025 : RatCutBinCertificate := ⟨⟨retention1025,(1102754281042186467/500000000000000000),(26755931122933953/200000000000000000),(34586963781175297/2500000000000000),(59077136701526038033/250000000000000000),(1022881741371103917/1000000000000000000)⟩,(495945778655119639/500000000000000000),(23738065257217489/50000000000000000),(42892101598000217/250000000000000000),(142878124114089093/1000000000000000000)⟩
theorem valid1025 : certificate1025.Valid := by decide +kernel
theorem sound1025 : certificate1025.Sound := rat_cut_bin_certificate_sound certificate1025 profilesValid1025 numericValid1025 valid1025

def retention1026 : RatCutRetentionCertificate := ⟨(209/4000),(21/400),(8383386723971196536/17055936265939102859),(3870958493584177667/500000000000000000),(21/20),(444911194479334353413418678276303147953/442395256409620304800000000000000000000),false,MergedCutProfiles.Batch172.profile6887,(fun _ => MergedCutProfiles.Batch172.profile6887)⟩
theorem profilesValid1026 : retention1026.ProfilesValid := by
  exact MergedCutProfiles.Batch172.valid6887
theorem numericValid1026 : retention1026.NumericValid := by decide +kernel
def certificate1026 : RatCutBinCertificate := ⟨⟨retention1026,(1102754281042186467/500000000000000000),(26755931122933953/200000000000000000),(34586963781175297/2500000000000000),(59077136701526038033/250000000000000000),(39331693863256443/40000000000000000)⟩,(495945778655119639/500000000000000000),(472734604277671483/1000000000000000000),(43270626645955989/250000000000000000),(72043733533379491/500000000000000000)⟩
theorem valid1026 : certificate1026.Valid := by decide +kernel
theorem sound1026 : certificate1026.Sound := rat_cut_bin_certificate_sound certificate1026 profilesValid1026 numericValid1026 valid1026

def retention1027 : RatCutRetentionCertificate := ⟨(209/4000),(21/400),(8467220591210908502/17055936265939102859),(1047923340496399567/125000000000000000),(21/20),(209236338288308698099406341744886525831/209584668099279913400000000000000000000),false,MergedCutProfiles.Batch172.profile6888,(fun _ => MergedCutProfiles.Batch172.profile6888)⟩
theorem profilesValid1027 : retention1027.ProfilesValid := by
  exact MergedCutProfiles.Batch172.valid6888
theorem numericValid1027 : retention1027.NumericValid := by decide +kernel
def certificate1027 : RatCutBinCertificate := ⟨⟨retention1027,(1102754281042186467/500000000000000000),(26755931122933953/200000000000000000),(34586963781175297/2500000000000000),(59077136701526038033/250000000000000000),(975943383535993729/1000000000000000000)⟩,(495945778655119639/500000000000000000),(473765980312230591/1000000000000000000),(6892436265334509/40000000000000000),(143615802941222557/1000000000000000000)⟩
theorem valid1027 : certificate1027.Valid := by decide +kernel
theorem sound1027 : certificate1027.Sound := rat_cut_bin_certificate_sound certificate1027 profilesValid1027 numericValid1027 valid1027

def retention1028 : RatCutRetentionCertificate := ⟨(209/4000),(21/400),(1/2),(4233610295605454251/500000000000000000),(21/20),(3358755035851787800524564665091542279879/3386888236484363400800000000000000000000),false,MergedCutProfiles.Batch172.profile6889,(fun _ => MergedCutProfiles.Batch172.profile6889)⟩
theorem profilesValid1028 : retention1028.ProfilesValid := by
  exact MergedCutProfiles.Batch172.valid6889
theorem numericValid1028 : retention1028.NumericValid := by decide +kernel
def certificate1028 : RatCutBinCertificate := ⟨⟨retention1028,(1102754281042186467/500000000000000000),(26755931122933953/200000000000000000),(34586963781175297/2500000000000000),(59077136701526038033/250000000000000000),(969298894252162989/1000000000000000000)⟩,(495945778655119639/500000000000000000),(238354710039449217/500000000000000000),(85060585441749497/500000000000000000),(35262535814273609/250000000000000000)⟩
theorem valid1028 : certificate1028.Valid := by decide +kernel
theorem sound1028 : certificate1028.Sound := rat_cut_bin_certificate_sound certificate1028 profilesValid1028 numericValid1028 valid1028

def retention1029 : RatCutRetentionCertificate := ⟨(209/4000),(21/400),(1/2),64,1,(62352874936955737581792525182498799/62500000000000000000000000000000000),false,MergedCutProfiles.Batch172.profile6889,(fun _ => MergedCutProfiles.Batch172.profile6889)⟩
theorem profilesValid1029 : retention1029.ProfilesValid := by
  exact MergedCutProfiles.Batch172.valid6889
theorem numericValid1029 : retention1029.NumericValid := by decide +kernel
def certificate1029 : RatCutBinCertificate := ⟨⟨retention1029,(1102754281042186467/500000000000000000),(26755931122933953/200000000000000000),(34586963781175297/2500000000000000),(59077136701526038033/250000000000000000),(976318976208126623/1000000000000000000)⟩,(495945778655119639/500000000000000000),(447076135747267839/1000000000000000000),(193015477462412971/1000000000000000000),(184094422557238827/1000000000000000000)⟩
theorem valid1029 : certificate1029.Valid := by decide +kernel
theorem sound1029 : certificate1029.Sound := rat_cut_bin_certificate_sound certificate1029 profilesValid1029 numericValid1029 valid1029

def retention1030 : RatCutRetentionCertificate := ⟨(209/4000),(21/400),(7727887238220093928/17055936265939102859),(3700659408711074843/1000000000000000000),(6/5),(100619522667040074666036959275695068549/92516485217776871075000000000000000000),false,MergedCutProfiles.Batch172.profile6890,(fun _ => MergedCutProfiles.Batch172.profile6890)⟩
theorem profilesValid1030 : retention1030.ProfilesValid := by
  exact MergedCutProfiles.Batch172.valid6890
theorem numericValid1030 : retention1030.NumericValid := by decide +kernel
def certificate1030 : RatCutBinCertificate := ⟨⟨retention1030,(1280862713542186467/500000000000000000),(26755931122933953/200000000000000000),(34586963781175297/2500000000000000),(59077136701526038033/250000000000000000),(1057855348710283573/1000000000000000000)⟩,(39623202511761841/40000000000000000),(94855146380745353/250000000000000000),(63219164779015913/250000000000000000),(184080049893387077/1000000000000000000)⟩
theorem valid1030 : certificate1030.Valid := by decide +kernel
theorem sound1030 : certificate1030.Sound := rat_cut_bin_certificate_sound certificate1030 profilesValid1030 numericValid1030 valid1030

def retention1031 : RatCutRetentionCertificate := ⟨(209/4000),(21/400),(8451876461406736101/17055936265939102859),(965985904777511741/125000000000000000),(21/20),(192792471191993938693287983517448952399/193197180955502348200000000000000000000),false,MergedCutProfiles.Batch172.profile6891,(fun _ => MergedCutProfiles.Batch172.profile6891)⟩
theorem profilesValid1031 : retention1031.ProfilesValid := by
  exact MergedCutProfiles.Batch172.valid6891
theorem numericValid1031 : retention1031.NumericValid := by decide +kernel
def certificate1031 : RatCutBinCertificate := ⟨⟨retention1031,(1280862713542186467/500000000000000000),(26755931122933953/200000000000000000),(34586963781175297/2500000000000000),(59077136701526038033/250000000000000000),(121486679185834639/125000000000000000)⟩,(39623202511761841/40000000000000000),(412979532505273947/1000000000000000000),(3465595655003337/15625000000000000),(182444654678197143/1000000000000000000)⟩
theorem valid1031 : certificate1031.Valid := by decide +kernel
theorem sound1031 : certificate1031.Sound := rat_cut_bin_certificate_sound certificate1031 profilesValid1031 numericValid1031 valid1031

def certificates : List RatCutBinCertificate := [certificate1020,certificate1021,certificate1022,certificate1023,certificate1024,certificate1025,certificate1026,certificate1027,certificate1028,certificate1029,certificate1030,certificate1031]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound1020,List.forall_mem_cons.mpr ⟨sound1021,List.forall_mem_cons.mpr ⟨sound1022,List.forall_mem_cons.mpr ⟨sound1023,List.forall_mem_cons.mpr ⟨sound1024,List.forall_mem_cons.mpr ⟨sound1025,List.forall_mem_cons.mpr ⟨sound1026,List.forall_mem_cons.mpr ⟨sound1027,List.forall_mem_cons.mpr ⟨sound1028,List.forall_mem_cons.mpr ⟨sound1029,List.forall_mem_cons.mpr ⟨sound1030,List.forall_mem_cons.mpr ⟨sound1031,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch085
