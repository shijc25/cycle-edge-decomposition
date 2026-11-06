import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch025
import Cycle12.MergedCutProfiles.Batch026
import Cycle12.MergedCutProfiles.Batch027
import Cycle12.MergedCutProfiles.Batch321
import Cycle12.MergedCutProfiles.Batch322
import Cycle12.MergedCutProfiles.Batch323

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch172

def retention2064 : RatCutRetentionCertificate := ⟨(1/50),(21/1000),(597210675000000000/125904482924188692167),(160784022328465993/250000000000000000),4,(145792535015018812333/64000000000000000000),true,MergedCutProfiles.Batch321.profile12849,![MergedCutProfiles.Batch321.profile12849,MergedCutProfiles.Batch025.profile1026,MergedCutProfiles.Batch321.profile12850,MergedCutProfiles.Batch321.profile12851,MergedCutProfiles.Batch321.profile12852,MergedCutProfiles.Batch321.profile12853,MergedCutProfiles.Batch321.profile12845,MergedCutProfiles.Batch321.profile12854,MergedCutProfiles.Batch025.profile1017,MergedCutProfiles.Batch321.profile12855,MergedCutProfiles.Batch321.profile12856,MergedCutProfiles.Batch321.profile12857,MergedCutProfiles.Batch321.profile12858,MergedCutProfiles.Batch321.profile12859,MergedCutProfiles.Batch321.profile12860,MergedCutProfiles.Batch321.profile12861]⟩
theorem profilesValid2064 : retention2064.ProfilesValid := by
  change ∀ j : Fin 16, (retention2064.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch321.valid12849
  · exact MergedCutProfiles.Batch025.valid1026
  · exact MergedCutProfiles.Batch321.valid12850
  · exact MergedCutProfiles.Batch321.valid12851
  · exact MergedCutProfiles.Batch321.valid12852
  · exact MergedCutProfiles.Batch321.valid12853
  · exact MergedCutProfiles.Batch321.valid12845
  · exact MergedCutProfiles.Batch321.valid12854
  · exact MergedCutProfiles.Batch025.valid1017
  · exact MergedCutProfiles.Batch321.valid12855
  · exact MergedCutProfiles.Batch321.valid12856
  · exact MergedCutProfiles.Batch321.valid12857
  · exact MergedCutProfiles.Batch321.valid12858
  · exact MergedCutProfiles.Batch321.valid12859
  · exact MergedCutProfiles.Batch321.valid12860
  · exact MergedCutProfiles.Batch321.valid12861
theorem numericValid2064 : retention2064.NumericValid := by decide +kernel
def certificate2064 : RatCutBinCertificate := ⟨⟨retention2064,(1897335656472775499/1000000000000000000),(1860584005120499/100000000000000000),(8545922877877615579/1000000000000000000),(2162263568793696880991/1000000000000000000),(2261485092395182879/1000000000000000000)⟩,(499568632545310609/500000000000000000),(510998402793355697/1000000000000000000),(36480737814787257/250000000000000000),(33783828531368581/500000000000000000)⟩
theorem valid2064 : certificate2064.Valid := by decide +kernel
theorem sound2064 : certificate2064.Sound := rat_cut_bin_certificate_sound certificate2064 profilesValid2064 numericValid2064 valid2064

def retention2065 : RatCutRetentionCertificate := ⟨(1/50),(21/1000),(1203786389835699467/251808965848377384334),(23888427/20000000),(5/2),(36428643206764176649/16000000000000000000),true,MergedCutProfiles.Batch321.profile12849,![MergedCutProfiles.Batch321.profile12849,MergedCutProfiles.Batch321.profile12862,MergedCutProfiles.Batch321.profile12850,MergedCutProfiles.Batch321.profile12851,MergedCutProfiles.Batch321.profile12863,MergedCutProfiles.Batch321.profile12853,MergedCutProfiles.Batch321.profile12845,MergedCutProfiles.Batch321.profile12847,MergedCutProfiles.Batch321.profile12864,MergedCutProfiles.Batch321.profile12855,MergedCutProfiles.Batch026.profile1040,MergedCutProfiles.Batch321.profile12857,MergedCutProfiles.Batch321.profile12858,MergedCutProfiles.Batch321.profile12865,MergedCutProfiles.Batch321.profile12866,MergedCutProfiles.Batch321.profile12861]⟩
theorem profilesValid2065 : retention2065.ProfilesValid := by
  change ∀ j : Fin 16, (retention2065.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch321.valid12849
  · exact MergedCutProfiles.Batch321.valid12862
  · exact MergedCutProfiles.Batch321.valid12850
  · exact MergedCutProfiles.Batch321.valid12851
  · exact MergedCutProfiles.Batch321.valid12863
  · exact MergedCutProfiles.Batch321.valid12853
  · exact MergedCutProfiles.Batch321.valid12845
  · exact MergedCutProfiles.Batch321.valid12847
  · exact MergedCutProfiles.Batch321.valid12864
  · exact MergedCutProfiles.Batch321.valid12855
  · exact MergedCutProfiles.Batch026.valid1040
  · exact MergedCutProfiles.Batch321.valid12857
  · exact MergedCutProfiles.Batch321.valid12858
  · exact MergedCutProfiles.Batch321.valid12865
  · exact MergedCutProfiles.Batch321.valid12866
  · exact MergedCutProfiles.Batch321.valid12861
theorem numericValid2065 : retention2065.NumericValid := by decide +kernel
def certificate2065 : RatCutBinCertificate := ⟨⟨retention2065,(1897335656472775499/1000000000000000000),(1860584005120499/100000000000000000),(8545922877877615579/1000000000000000000),(2162263568793696880991/1000000000000000000),(226646316319714019/100000000000000000)⟩,(499568632545310609/500000000000000000),(364181560631662331/1000000000000000000),(53590754320409809/200000000000000000),(186163512955609849/1000000000000000000)⟩
theorem valid2065 : certificate2065.Valid := by decide +kernel
theorem sound2065 : certificate2065.Sound := rat_cut_bin_certificate_sound certificate2065 profilesValid2065 numericValid2065 valid2065

def retention2066 : RatCutRetentionCertificate := ⟨(1/50),(21/1000),(756677865646303986/125904482924188692167),(1203786389835699467/1000000000000000000),(5/2),(580936654468519071179/256000000000000000000),true,MergedCutProfiles.Batch321.profile12867,![MergedCutProfiles.Batch321.profile12867,MergedCutProfiles.Batch321.profile12868,MergedCutProfiles.Batch321.profile12840,MergedCutProfiles.Batch321.profile12863,MergedCutProfiles.Batch321.profile12869,MergedCutProfiles.Batch321.profile12870,MergedCutProfiles.Batch025.profile1017,MergedCutProfiles.Batch025.profile1018,MergedCutProfiles.Batch321.profile12871,MergedCutProfiles.Batch321.profile12872,MergedCutProfiles.Batch321.profile12859,MergedCutProfiles.Batch321.profile12866,MergedCutProfiles.Batch321.profile12873,MergedCutProfiles.Batch321.profile12874,MergedCutProfiles.Batch321.profile12875,MergedCutProfiles.Batch026.profile1041]⟩
theorem profilesValid2066 : retention2066.ProfilesValid := by
  change ∀ j : Fin 16, (retention2066.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch321.valid12867
  · exact MergedCutProfiles.Batch321.valid12868
  · exact MergedCutProfiles.Batch321.valid12840
  · exact MergedCutProfiles.Batch321.valid12863
  · exact MergedCutProfiles.Batch321.valid12869
  · exact MergedCutProfiles.Batch321.valid12870
  · exact MergedCutProfiles.Batch025.valid1017
  · exact MergedCutProfiles.Batch025.valid1018
  · exact MergedCutProfiles.Batch321.valid12871
  · exact MergedCutProfiles.Batch321.valid12872
  · exact MergedCutProfiles.Batch321.valid12859
  · exact MergedCutProfiles.Batch321.valid12866
  · exact MergedCutProfiles.Batch321.valid12873
  · exact MergedCutProfiles.Batch321.valid12874
  · exact MergedCutProfiles.Batch321.valid12875
  · exact MergedCutProfiles.Batch026.valid1041
theorem numericValid2066 : retention2066.NumericValid := by decide +kernel
def certificate2066 : RatCutBinCertificate := ⟨⟨retention2066,(1897335656472775499/1000000000000000000),(1860584005120499/100000000000000000),(8545922877877615579/1000000000000000000),(2162263568793696880991/1000000000000000000),(35296199523805407/15625000000000000)⟩,(499568632545310609/500000000000000000),(182032511659767141/500000000000000000),(268071491859590787/1000000000000000000),(18610822248242097/100000000000000000)⟩
theorem valid2066 : certificate2066.Valid := by decide +kernel
theorem sound2066 : certificate2066.Sound := rat_cut_bin_certificate_sound certificate2066 profilesValid2066 numericValid2066 valid2066

def retention2067 : RatCutRetentionCertificate := ⟨(1/50),(21/1000),(8160548762624679260/125904482924188692167),(378338932823151993/250000000000000000),(43/20),(640268766951016709421/320000000000000000000),true,MergedCutProfiles.Batch025.profile1031,![MergedCutProfiles.Batch025.profile1031,MergedCutProfiles.Batch321.profile12876,MergedCutProfiles.Batch026.profile1050,MergedCutProfiles.Batch321.profile12877,MergedCutProfiles.Batch321.profile12878,MergedCutProfiles.Batch026.profile1054,MergedCutProfiles.Batch321.profile12879,MergedCutProfiles.Batch322.profile12880,MergedCutProfiles.Batch026.profile1058,MergedCutProfiles.Batch322.profile12881,MergedCutProfiles.Batch322.profile12882,MergedCutProfiles.Batch026.profile1062,MergedCutProfiles.Batch322.profile12883,MergedCutProfiles.Batch322.profile12884,MergedCutProfiles.Batch322.profile12885,MergedCutProfiles.Batch322.profile12886]⟩
theorem profilesValid2067 : retention2067.ProfilesValid := by
  change ∀ j : Fin 16, (retention2067.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch025.valid1031
  · exact MergedCutProfiles.Batch321.valid12876
  · exact MergedCutProfiles.Batch026.valid1050
  · exact MergedCutProfiles.Batch321.valid12877
  · exact MergedCutProfiles.Batch321.valid12878
  · exact MergedCutProfiles.Batch026.valid1054
  · exact MergedCutProfiles.Batch321.valid12879
  · exact MergedCutProfiles.Batch322.valid12880
  · exact MergedCutProfiles.Batch026.valid1058
  · exact MergedCutProfiles.Batch322.valid12881
  · exact MergedCutProfiles.Batch322.valid12882
  · exact MergedCutProfiles.Batch026.valid1062
  · exact MergedCutProfiles.Batch322.valid12883
  · exact MergedCutProfiles.Batch322.valid12884
  · exact MergedCutProfiles.Batch322.valid12885
  · exact MergedCutProfiles.Batch322.valid12886
theorem numericValid2067 : retention2067.NumericValid := by decide +kernel
def certificate2067 : RatCutBinCertificate := ⟨⟨retention2067,(1897335656472775499/1000000000000000000),(1860584005120499/100000000000000000),(8545922877877615579/1000000000000000000),(2162263568793696880991/1000000000000000000),(995979323406616939/500000000000000000)⟩,(499568632545310609/500000000000000000),(373611456168000863/1000000000000000000),(32318822729987099/125000000000000000),(1455242130655619/7812500000000000)⟩
theorem valid2067 : certificate2067.Valid := by decide +kernel
theorem sound2067 : certificate2067.Sound := rat_cut_bin_certificate_sound certificate2067 profilesValid2067 numericValid2067 valid2067

def retention2068 : RatCutRetentionCertificate := ⟨(1/50),(21/1000),(32000000000000000000/125904482924188692167),(408027438131233963/25000000000000000),1,(96537565222193206133735353812914196039/65284390100997434080000000000000000000),false,MergedCutProfiles.Batch322.profile12887,(fun _ => MergedCutProfiles.Batch322.profile12887)⟩
theorem profilesValid2068 : retention2068.ProfilesValid := by
  exact MergedCutProfiles.Batch322.valid12887
theorem numericValid2068 : retention2068.NumericValid := by decide +kernel
def certificate2068 : RatCutBinCertificate := ⟨⟨retention2068,(1897335656472775499/1000000000000000000),(1860584005120499/100000000000000000),(8545922877877615579/1000000000000000000),(2162263568793696880991/1000000000000000000),(1474592746864482623/1000000000000000000)⟩,(499568632545310609/500000000000000000),(79406289353292351/250000000000000000),(318081547634502123/1000000000000000000),(429792410092839913/1000000000000000000)⟩
theorem valid2068 : certificate2068.Valid := by decide +kernel
theorem sound2068 : certificate2068.Sound := rat_cut_bin_certificate_sound certificate2068 profilesValid2068 numericValid2068 valid2068

def retention2069 : RatCutRetentionCertificate := ⟨(1/50),(21/1000),(1/2),64,1,(3990181166188230871926367807584118119/4000000000000000000000000000000000000),false,MergedCutProfiles.Batch026.profile1066,(fun _ => MergedCutProfiles.Batch026.profile1066)⟩
theorem profilesValid2069 : retention2069.ProfilesValid := by
  exact MergedCutProfiles.Batch026.valid1066
theorem numericValid2069 : retention2069.NumericValid := by decide +kernel
def certificate2069 : RatCutBinCertificate := ⟨⟨retention2069,(1897335656472775499/1000000000000000000),(1860584005120499/100000000000000000),(8545922877877615579/1000000000000000000),(2162263568793696880991/1000000000000000000),(49670724400250117/50000000000000000)⟩,(499568632545310609/500000000000000000),(225165413880866901/500000000000000000),(23800901727082673/125000000000000000),(93050030346552967/500000000000000000)⟩
theorem valid2069 : certificate2069.Valid := by decide +kernel
theorem sound2069 : certificate2069.Sound := rat_cut_bin_certificate_sound certificate2069 profilesValid2069 numericValid2069 valid2069

def retention2070 : RatCutRetentionCertificate := ⟨(1/50),(21/1000),(32000000000000000000/125904482924188692167),(5229569777229043149/1000000000000000000),(11/10),(1022827388668510199079856973541624592293/697275970297205753200000000000000000000),false,MergedCutProfiles.Batch322.profile12887,(fun _ => MergedCutProfiles.Batch322.profile12887)⟩
theorem profilesValid2070 : retention2070.ProfilesValid := by
  exact MergedCutProfiles.Batch322.valid12887
theorem numericValid2070 : retention2070.NumericValid := by decide +kernel
def certificate2070 : RatCutBinCertificate := ⟨⟨retention2070,(2195216464472775499/1000000000000000000),(1860584005120499/100000000000000000),(8545922877877615579/1000000000000000000),(2162263568793696880991/1000000000000000000),(58465322654498537/40000000000000000)⟩,(999001813802302053/1000000000000000000),(1299881087747221/8000000000000000),(135377550194183057/250000000000000000),(36493567526185481/62500000000000000)⟩
theorem valid2070 : certificate2070.Valid := by decide +kernel
theorem sound2070 : certificate2070.Sound := rat_cut_bin_certificate_sound certificate2070 profilesValid2070 numericValid2070 valid2070

def retention2071 : RatCutRetentionCertificate := ⟨(1/50),(21/1000),(1/2),64,1,(3990181166188230871926367807584118119/4000000000000000000000000000000000000),false,MergedCutProfiles.Batch026.profile1066,(fun _ => MergedCutProfiles.Batch026.profile1066)⟩
theorem profilesValid2071 : retention2071.ProfilesValid := by
  exact MergedCutProfiles.Batch026.valid1066
theorem numericValid2071 : retention2071.NumericValid := by decide +kernel
def certificate2071 : RatCutBinCertificate := ⟨⟨retention2071,(2195216464472775499/1000000000000000000),(1860584005120499/100000000000000000),(8545922877877615579/1000000000000000000),(2162263568793696880991/1000000000000000000),(124095744223339543/125000000000000000)⟩,(999001813802302053/1000000000000000000),(29903025811111863/125000000000000000),(104622214744126949/250000000000000000),(408703969115435349/1000000000000000000)⟩
theorem valid2071 : certificate2071.Valid := by decide +kernel
theorem sound2071 : certificate2071.Sound := rat_cut_bin_certificate_sound certificate2071 profilesValid2071 numericValid2071 valid2071

def retention2072 : RatCutRetentionCertificate := ⟨(21/1000),(11/500),(641339063155535775/228335710556315594062),(634989171441124529/1000000000000000000),4,(585284478668862851017/256000000000000000000),true,MergedCutProfiles.Batch322.profile12888,![MergedCutProfiles.Batch322.profile12888,MergedCutProfiles.Batch322.profile12889,MergedCutProfiles.Batch322.profile12890,MergedCutProfiles.Batch027.profile1100,MergedCutProfiles.Batch322.profile12891,MergedCutProfiles.Batch322.profile12892,MergedCutProfiles.Batch322.profile12893,MergedCutProfiles.Batch027.profile1101,MergedCutProfiles.Batch322.profile12894,MergedCutProfiles.Batch322.profile12895,MergedCutProfiles.Batch322.profile12896,MergedCutProfiles.Batch322.profile12897,MergedCutProfiles.Batch322.profile12898,MergedCutProfiles.Batch322.profile12899,MergedCutProfiles.Batch322.profile12900,MergedCutProfiles.Batch027.profile1103]⟩
theorem profilesValid2072 : retention2072.ProfilesValid := by
  change ∀ j : Fin 16, (retention2072.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch322.valid12888
  · exact MergedCutProfiles.Batch322.valid12889
  · exact MergedCutProfiles.Batch322.valid12890
  · exact MergedCutProfiles.Batch027.valid1100
  · exact MergedCutProfiles.Batch322.valid12891
  · exact MergedCutProfiles.Batch322.valid12892
  · exact MergedCutProfiles.Batch322.valid12893
  · exact MergedCutProfiles.Batch027.valid1101
  · exact MergedCutProfiles.Batch322.valid12894
  · exact MergedCutProfiles.Batch322.valid12895
  · exact MergedCutProfiles.Batch322.valid12896
  · exact MergedCutProfiles.Batch322.valid12897
  · exact MergedCutProfiles.Batch322.valid12898
  · exact MergedCutProfiles.Batch322.valid12899
  · exact MergedCutProfiles.Batch322.valid12900
  · exact MergedCutProfiles.Batch027.valid1103
theorem numericValid2072 : retention2072.NumericValid := by decide +kernel
def certificate2072 : RatCutBinCertificate := ⟨⟨retention2072,(3824476810895587/2000000000000000),(10247703429141591/500000000000000000),(1731926382999934319/200000000000000000),(496711091993987075701/250000000000000000),(2268164063298417161/1000000000000000000)⟩,(499527720107808973/500000000000000000),(511372842006497633/1000000000000000000),(9104480910930279/62500000000000000),(13490335624341429/200000000000000000)⟩
theorem valid2072 : certificate2072.Valid := by decide +kernel
theorem sound2072 : certificate2072.Sound := rat_cut_bin_certificate_sound certificate2072 profilesValid2072 numericValid2072 valid2072

def retention2073 : RatCutRetentionCertificate := ⟨(21/1000),(11/500),(1142161120179245623/228335710556315594062),(25653562526221431/40000000000000000),4,(582445044120736810439/256000000000000000000),true,MergedCutProfiles.Batch322.profile12901,![MergedCutProfiles.Batch322.profile12901,MergedCutProfiles.Batch027.profile1085,MergedCutProfiles.Batch322.profile12902,MergedCutProfiles.Batch027.profile1086,MergedCutProfiles.Batch322.profile12903,MergedCutProfiles.Batch026.profile1073,MergedCutProfiles.Batch322.profile12904,MergedCutProfiles.Batch027.profile1087,MergedCutProfiles.Batch027.profile1103,MergedCutProfiles.Batch027.profile1088,MergedCutProfiles.Batch322.profile12905,MergedCutProfiles.Batch027.profile1089,MergedCutProfiles.Batch026.profile1079,MergedCutProfiles.Batch027.profile1090,MergedCutProfiles.Batch322.profile12906,MergedCutProfiles.Batch322.profile12907]⟩
theorem profilesValid2073 : retention2073.ProfilesValid := by
  change ∀ j : Fin 16, (retention2073.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch322.valid12901
  · exact MergedCutProfiles.Batch027.valid1085
  · exact MergedCutProfiles.Batch322.valid12902
  · exact MergedCutProfiles.Batch027.valid1086
  · exact MergedCutProfiles.Batch322.valid12903
  · exact MergedCutProfiles.Batch026.valid1073
  · exact MergedCutProfiles.Batch322.valid12904
  · exact MergedCutProfiles.Batch027.valid1087
  · exact MergedCutProfiles.Batch027.valid1103
  · exact MergedCutProfiles.Batch027.valid1088
  · exact MergedCutProfiles.Batch322.valid12905
  · exact MergedCutProfiles.Batch027.valid1089
  · exact MergedCutProfiles.Batch026.valid1079
  · exact MergedCutProfiles.Batch027.valid1090
  · exact MergedCutProfiles.Batch322.valid12906
  · exact MergedCutProfiles.Batch322.valid12907
theorem numericValid2073 : retention2073.NumericValid := by decide +kernel
def certificate2073 : RatCutBinCertificate := ⟨⟨retention2073,(3824476810895587/2000000000000000),(10247703429141591/500000000000000000),(1731926382999934319/200000000000000000),(496711091993987075701/250000000000000000),(2257072522822754171/1000000000000000000)⟩,(499527720107808973/500000000000000000),(510734353534915673/1000000000000000000),(146100298881741303/1000000000000000000),(67501021945351163/1000000000000000000)⟩
theorem valid2073 : certificate2073.Valid := by decide +kernel
theorem sound2073 : certificate2073.Sound := rat_cut_bin_certificate_sound certificate2073 profilesValid2073 numericValid2073 valid2073

def retention2074 : RatCutRetentionCertificate := ⟨(21/1000),(11/500),(602956270000000000/114167855278157797031),(1142161120179245623/1000000000000000000),(13/5),(2915706098524494659787/1280000000000000000000),true,MergedCutProfiles.Batch322.profile12908,![MergedCutProfiles.Batch322.profile12908,MergedCutProfiles.Batch322.profile12909,MergedCutProfiles.Batch322.profile12910,MergedCutProfiles.Batch322.profile12911,MergedCutProfiles.Batch322.profile12912,MergedCutProfiles.Batch322.profile12913,MergedCutProfiles.Batch322.profile12914,MergedCutProfiles.Batch322.profile12900,MergedCutProfiles.Batch026.profile1076,MergedCutProfiles.Batch322.profile12915,MergedCutProfiles.Batch322.profile12916,MergedCutProfiles.Batch322.profile12917,MergedCutProfiles.Batch322.profile12918,MergedCutProfiles.Batch322.profile12919,MergedCutProfiles.Batch322.profile12907,MergedCutProfiles.Batch027.profile1114]⟩
theorem profilesValid2074 : retention2074.ProfilesValid := by
  change ∀ j : Fin 16, (retention2074.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch322.valid12908
  · exact MergedCutProfiles.Batch322.valid12909
  · exact MergedCutProfiles.Batch322.valid12910
  · exact MergedCutProfiles.Batch322.valid12911
  · exact MergedCutProfiles.Batch322.valid12912
  · exact MergedCutProfiles.Batch322.valid12913
  · exact MergedCutProfiles.Batch322.valid12914
  · exact MergedCutProfiles.Batch322.valid12900
  · exact MergedCutProfiles.Batch026.valid1076
  · exact MergedCutProfiles.Batch322.valid12915
  · exact MergedCutProfiles.Batch322.valid12916
  · exact MergedCutProfiles.Batch322.valid12917
  · exact MergedCutProfiles.Batch322.valid12918
  · exact MergedCutProfiles.Batch322.valid12919
  · exact MergedCutProfiles.Batch322.valid12907
  · exact MergedCutProfiles.Batch027.valid1114
theorem numericValid2074 : retention2074.NumericValid := by decide +kernel
def certificate2074 : RatCutBinCertificate := ⟨⟨retention2074,(3824476810895587/2000000000000000),(10247703429141591/500000000000000000),(1731926382999934319/200000000000000000),(496711091993987075701/250000000000000000),(1133064082955322759/500000000000000000)⟩,(499527720107808973/500000000000000000),(371059302948010949/1000000000000000000),(32633973143693831/125000000000000000),(175725817871407407/1000000000000000000)⟩
theorem valid2074 : certificate2074.Valid := by decide +kernel
theorem sound2074 : certificate2074.Sound := rat_cut_bin_certificate_sound certificate2074 profilesValid2074 numericValid2074 valid2074

def retention2075 : RatCutRetentionCertificate := ⟨(21/1000),(11/500),(867351383685669383/114167855278157797031),(60295627/50000000),(5/2),(18071517404441272141/8000000000000000000),true,MergedCutProfiles.Batch323.profile12920,![MergedCutProfiles.Batch323.profile12920,MergedCutProfiles.Batch323.profile12921,MergedCutProfiles.Batch323.profile12922,MergedCutProfiles.Batch322.profile12896,MergedCutProfiles.Batch323.profile12923,MergedCutProfiles.Batch323.profile12924,MergedCutProfiles.Batch026.profile1077,MergedCutProfiles.Batch323.profile12925,MergedCutProfiles.Batch027.profile1105,MergedCutProfiles.Batch323.profile12926,MergedCutProfiles.Batch027.profile1114,MergedCutProfiles.Batch323.profile12927,MergedCutProfiles.Batch323.profile12928,MergedCutProfiles.Batch323.profile12929,MergedCutProfiles.Batch323.profile12930,MergedCutProfiles.Batch323.profile12931]⟩
theorem profilesValid2075 : retention2075.ProfilesValid := by
  change ∀ j : Fin 16, (retention2075.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch323.valid12920
  · exact MergedCutProfiles.Batch323.valid12921
  · exact MergedCutProfiles.Batch323.valid12922
  · exact MergedCutProfiles.Batch322.valid12896
  · exact MergedCutProfiles.Batch323.valid12923
  · exact MergedCutProfiles.Batch323.valid12924
  · exact MergedCutProfiles.Batch026.valid1077
  · exact MergedCutProfiles.Batch323.valid12925
  · exact MergedCutProfiles.Batch027.valid1105
  · exact MergedCutProfiles.Batch323.valid12926
  · exact MergedCutProfiles.Batch027.valid1114
  · exact MergedCutProfiles.Batch323.valid12927
  · exact MergedCutProfiles.Batch323.valid12928
  · exact MergedCutProfiles.Batch323.valid12929
  · exact MergedCutProfiles.Batch323.valid12930
  · exact MergedCutProfiles.Batch323.valid12931
theorem numericValid2075 : retention2075.NumericValid := by decide +kernel
def certificate2075 : RatCutBinCertificate := ⟨⟨retention2075,(3824476810895587/2000000000000000),(10247703429141591/500000000000000000),(1731926382999934319/200000000000000000),(496711091993987075701/250000000000000000),(2247625038103923201/1000000000000000000)⟩,(499527720107808973/500000000000000000),(182359831474644413/500000000000000000),(53482138006408327/200000000000000000),(184990264774888927/1000000000000000000)⟩
theorem valid2075 : certificate2075.Valid := by decide +kernel
theorem sound2075 : certificate2075.Sound := rat_cut_bin_certificate_sound certificate2075 profilesValid2075 numericValid2075 valid2075

def certificates : List RatCutBinCertificate := [certificate2064,certificate2065,certificate2066,certificate2067,certificate2068,certificate2069,certificate2070,certificate2071,certificate2072,certificate2073,certificate2074,certificate2075]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound2064,List.forall_mem_cons.mpr ⟨sound2065,List.forall_mem_cons.mpr ⟨sound2066,List.forall_mem_cons.mpr ⟨sound2067,List.forall_mem_cons.mpr ⟨sound2068,List.forall_mem_cons.mpr ⟨sound2069,List.forall_mem_cons.mpr ⟨sound2070,List.forall_mem_cons.mpr ⟨sound2071,List.forall_mem_cons.mpr ⟨sound2072,List.forall_mem_cons.mpr ⟨sound2073,List.forall_mem_cons.mpr ⟨sound2074,List.forall_mem_cons.mpr ⟨sound2075,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch172
