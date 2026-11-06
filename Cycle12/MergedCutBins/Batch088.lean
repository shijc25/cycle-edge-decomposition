import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch176
import Cycle12.MergedCutProfiles.Batch177
import Cycle12.MergedCutProfiles.Batch178

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch088

def retention1056 : RatCutRetentionCertificate := ⟨(211/4000),(53/1000),(8312968170779165699/16686931111337825223),(8230661555226896731/1000000000000000000),(21/20),(13096927354272245648328479435067811620239/13169058488363034769600000000000000000000),false,MergedCutProfiles.Batch176.profile7059,(fun _ => MergedCutProfiles.Batch176.profile7059)⟩
theorem profilesValid1056 : retention1056.ProfilesValid := by
  exact MergedCutProfiles.Batch176.valid7059
theorem numericValid1056 : retention1056.NumericValid := by decide +kernel
def certificate1056 : RatCutBinCertificate := ⟨⟨retention1056,(641619588397843647/250000000000000000),(136712609017002193/1000000000000000000),(6976658962883345709/500000000000000000),(116588969202694662563/500000000000000000),(968117603377964939/1000000000000000000)⟩,(495233720560450649/500000000000000000),(102987301006079663/250000000000000000),(1781684460219141/8000000000000000),(183684083915986841/1000000000000000000)⟩
theorem valid1056 : certificate1056.Valid := by decide +kernel
theorem sound1056 : certificate1056.Sound := rat_cut_bin_certificate_sound certificate1056 profilesValid1056 numericValid1056 valid1056

def retention1057 : RatCutRetentionCertificate := ⟨(211/4000),(53/1000),(1/2),(8312968170779165699/1000000000000000000),(21/20),(13184271054363453357952818241617183956759/13300749073246665118400000000000000000000),false,MergedCutProfiles.Batch176.profile7056,(fun _ => MergedCutProfiles.Batch176.profile7056)⟩
theorem profilesValid1057 : retention1057.ProfilesValid := by
  exact MergedCutProfiles.Batch176.valid7056
theorem numericValid1057 : retention1057.NumericValid := by decide +kernel
def certificate1057 : RatCutBinCertificate := ⟨⟨retention1057,(641619588397843647/250000000000000000),(136712609017002193/1000000000000000000),(6976658962883345709/500000000000000000),(116588969202694662563/500000000000000000),(150755888677899/156250000000000)⟩,(495233720560450649/500000000000000000),(413349604046792137/1000000000000000000),(1107355112507867/5000000000000000),(36455328578238867/200000000000000000)⟩
theorem valid1057 : certificate1057.Valid := by decide +kernel
theorem sound1057 : certificate1057.Sound := rat_cut_bin_certificate_sound certificate1057 profilesValid1057 numericValid1057 valid1057

def retention1058 : RatCutRetentionCertificate := ⟨(53/1000),(213/4000),(851115183986928779/16506479533787880736),(421344150488578603/500000000000000000),(57/20),(20441736551746363179/10000000000000000000),true,MergedCutProfiles.Batch176.profile7060,![MergedCutProfiles.Batch176.profile7060,MergedCutProfiles.Batch176.profile7061,MergedCutProfiles.Batch176.profile7062,MergedCutProfiles.Batch176.profile7063,MergedCutProfiles.Batch176.profile7064,MergedCutProfiles.Batch176.profile7065,MergedCutProfiles.Batch176.profile7066,MergedCutProfiles.Batch176.profile7067,MergedCutProfiles.Batch176.profile7068,MergedCutProfiles.Batch176.profile7069,MergedCutProfiles.Batch176.profile7070,MergedCutProfiles.Batch176.profile7071,MergedCutProfiles.Batch176.profile7072,MergedCutProfiles.Batch176.profile7073,MergedCutProfiles.Batch176.profile7074,MergedCutProfiles.Batch176.profile7075]⟩
theorem profilesValid1058 : retention1058.ProfilesValid := by
  change ∀ j : Fin 16, (retention1058.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch176.valid7060
  · exact MergedCutProfiles.Batch176.valid7061
  · exact MergedCutProfiles.Batch176.valid7062
  · exact MergedCutProfiles.Batch176.valid7063
  · exact MergedCutProfiles.Batch176.valid7064
  · exact MergedCutProfiles.Batch176.valid7065
  · exact MergedCutProfiles.Batch176.valid7066
  · exact MergedCutProfiles.Batch176.valid7067
  · exact MergedCutProfiles.Batch176.valid7068
  · exact MergedCutProfiles.Batch176.valid7069
  · exact MergedCutProfiles.Batch176.valid7070
  · exact MergedCutProfiles.Batch176.valid7071
  · exact MergedCutProfiles.Batch176.valid7072
  · exact MergedCutProfiles.Batch176.valid7073
  · exact MergedCutProfiles.Batch176.valid7074
  · exact MergedCutProfiles.Batch176.valid7075
theorem numericValid1058 : retention1058.NumericValid := by decide +kernel
def certificate1058 : RatCutBinCertificate := ⟨⟨retention1058,(2215121588008153677/1000000000000000000),(138194877202670159/1000000000000000000),(14013165961528612701/1000000000000000000),(57911559766397994477/250000000000000000),(99094988406277209/50000000000000000)⟩,(15495838321839759/15625000000000000),(73431148230345989/200000000000000000),(132480987342570539/500000000000000000),(8842263187071097/62500000000000000)⟩
theorem valid1058 : certificate1058.Valid := by decide +kernel
theorem sound1058 : certificate1058.Sound := rat_cut_bin_certificate_sound certificate1058 profilesValid1058 numericValid1058 valid1058

def retention1059 : RatCutRetentionCertificate := ⟨(53/1000),(213/4000),(912510677467448489/16506479533787880736),(851115183986928779/1000000000000000000),(57/20),(2608156733982298548771/1280000000000000000000),true,MergedCutProfiles.Batch176.profile7076,![MergedCutProfiles.Batch176.profile7076,MergedCutProfiles.Batch176.profile7077,MergedCutProfiles.Batch176.profile7078,MergedCutProfiles.Batch176.profile7079,MergedCutProfiles.Batch177.profile7080,MergedCutProfiles.Batch177.profile7081,MergedCutProfiles.Batch177.profile7082,MergedCutProfiles.Batch177.profile7083,MergedCutProfiles.Batch177.profile7084,MergedCutProfiles.Batch177.profile7085,MergedCutProfiles.Batch177.profile7086,MergedCutProfiles.Batch177.profile7087,MergedCutProfiles.Batch177.profile7088,MergedCutProfiles.Batch176.profile7074,MergedCutProfiles.Batch177.profile7089,MergedCutProfiles.Batch177.profile7090]⟩
theorem profilesValid1059 : retention1059.ProfilesValid := by
  change ∀ j : Fin 16, (retention1059.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch176.valid7076
  · exact MergedCutProfiles.Batch176.valid7077
  · exact MergedCutProfiles.Batch176.valid7078
  · exact MergedCutProfiles.Batch176.valid7079
  · exact MergedCutProfiles.Batch177.valid7080
  · exact MergedCutProfiles.Batch177.valid7081
  · exact MergedCutProfiles.Batch177.valid7082
  · exact MergedCutProfiles.Batch177.valid7083
  · exact MergedCutProfiles.Batch177.valid7084
  · exact MergedCutProfiles.Batch177.valid7085
  · exact MergedCutProfiles.Batch177.valid7086
  · exact MergedCutProfiles.Batch177.valid7087
  · exact MergedCutProfiles.Batch177.valid7088
  · exact MergedCutProfiles.Batch176.valid7074
  · exact MergedCutProfiles.Batch177.valid7089
  · exact MergedCutProfiles.Batch177.valid7090
theorem numericValid1059 : retention1059.NumericValid := by decide +kernel
def certificate1059 : RatCutBinCertificate := ⟨⟨retention1059,(2215121588008153677/1000000000000000000),(138194877202670159/1000000000000000000),(14013165961528612701/1000000000000000000),(57911559766397994477/250000000000000000),(123459294655904119/62500000000000000)⟩,(15495838321839759/15625000000000000),(366874195123754131/1000000000000000000),(132622076995902903/500000000000000000),(70789548394869351/500000000000000000)⟩
theorem valid1059 : certificate1059.Valid := by decide +kernel
theorem sound1059 : certificate1059.Sound := rat_cut_bin_certificate_sound certificate1059 profilesValid1059 numericValid1059 valid1059

def retention1060 : RatCutRetentionCertificate := ⟨(53/1000),(213/4000),(124744554066839565/1500589048526170976),(912510677467448489/1000000000000000000),(53/20),(623560455704524557159/320000000000000000000),true,MergedCutProfiles.Batch177.profile7091,![MergedCutProfiles.Batch177.profile7091,MergedCutProfiles.Batch176.profile7078,MergedCutProfiles.Batch177.profile7092,MergedCutProfiles.Batch177.profile7093,MergedCutProfiles.Batch177.profile7094,MergedCutProfiles.Batch177.profile7084,MergedCutProfiles.Batch177.profile7095,MergedCutProfiles.Batch177.profile7087,MergedCutProfiles.Batch177.profile7096,MergedCutProfiles.Batch177.profile7089,MergedCutProfiles.Batch177.profile7097,MergedCutProfiles.Batch177.profile7098,MergedCutProfiles.Batch177.profile7099,MergedCutProfiles.Batch177.profile7100,MergedCutProfiles.Batch177.profile7101,MergedCutProfiles.Batch177.profile7102]⟩
theorem profilesValid1060 : retention1060.ProfilesValid := by
  change ∀ j : Fin 16, (retention1060.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch177.valid7091
  · exact MergedCutProfiles.Batch176.valid7078
  · exact MergedCutProfiles.Batch177.valid7092
  · exact MergedCutProfiles.Batch177.valid7093
  · exact MergedCutProfiles.Batch177.valid7094
  · exact MergedCutProfiles.Batch177.valid7084
  · exact MergedCutProfiles.Batch177.valid7095
  · exact MergedCutProfiles.Batch177.valid7087
  · exact MergedCutProfiles.Batch177.valid7096
  · exact MergedCutProfiles.Batch177.valid7089
  · exact MergedCutProfiles.Batch177.valid7097
  · exact MergedCutProfiles.Batch177.valid7098
  · exact MergedCutProfiles.Batch177.valid7099
  · exact MergedCutProfiles.Batch177.valid7100
  · exact MergedCutProfiles.Batch177.valid7101
  · exact MergedCutProfiles.Batch177.valid7102
theorem numericValid1060 : retention1060.NumericValid := by decide +kernel
def certificate1060 : RatCutBinCertificate := ⟨⟨retention1060,(2215121588008153677/1000000000000000000),(138194877202670159/1000000000000000000),(14013165961528612701/1000000000000000000),(57911559766397994477/250000000000000000),(378144546486764139/200000000000000000)⟩,(15495838321839759/15625000000000000),(186378342239254981/500000000000000000),(259393041913328049/1000000000000000000),(70750967848577723/500000000000000000)⟩
theorem valid1060 : certificate1060.Valid := by decide +kernel
theorem sound1060 : certificate1060.Sound := rat_cut_bin_certificate_sound certificate1060 profilesValid1060 numericValid1060 valid1060

def retention1061 : RatCutRetentionCertificate := ⟨(53/1000),(213/4000),(918692758622549089/4126619883446970184),(274438018947047043/200000000000000000),(39/20),(404825714927660826483/256000000000000000000),true,MergedCutProfiles.Batch177.profile7103,![MergedCutProfiles.Batch177.profile7103,MergedCutProfiles.Batch177.profile7104,MergedCutProfiles.Batch177.profile7105,MergedCutProfiles.Batch177.profile7106,MergedCutProfiles.Batch177.profile7107,MergedCutProfiles.Batch177.profile7108,MergedCutProfiles.Batch177.profile7109,MergedCutProfiles.Batch177.profile7110,MergedCutProfiles.Batch177.profile7111,MergedCutProfiles.Batch177.profile7112,MergedCutProfiles.Batch177.profile7113,MergedCutProfiles.Batch177.profile7114,MergedCutProfiles.Batch177.profile7115,MergedCutProfiles.Batch177.profile7116,MergedCutProfiles.Batch177.profile7117,MergedCutProfiles.Batch177.profile7118]⟩
theorem profilesValid1061 : retention1061.ProfilesValid := by
  change ∀ j : Fin 16, (retention1061.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch177.valid7103
  · exact MergedCutProfiles.Batch177.valid7104
  · exact MergedCutProfiles.Batch177.valid7105
  · exact MergedCutProfiles.Batch177.valid7106
  · exact MergedCutProfiles.Batch177.valid7107
  · exact MergedCutProfiles.Batch177.valid7108
  · exact MergedCutProfiles.Batch177.valid7109
  · exact MergedCutProfiles.Batch177.valid7110
  · exact MergedCutProfiles.Batch177.valid7111
  · exact MergedCutProfiles.Batch177.valid7112
  · exact MergedCutProfiles.Batch177.valid7113
  · exact MergedCutProfiles.Batch177.valid7114
  · exact MergedCutProfiles.Batch177.valid7115
  · exact MergedCutProfiles.Batch177.valid7116
  · exact MergedCutProfiles.Batch177.valid7117
  · exact MergedCutProfiles.Batch177.valid7118
theorem numericValid1061 : retention1061.NumericValid := by decide +kernel
def certificate1061 : RatCutBinCertificate := ⟨⟨retention1061,(2215121588008153677/1000000000000000000),(138194877202670159/1000000000000000000),(14013165961528612701/1000000000000000000),(57911559766397994477/250000000000000000),(1538743083872360307/1000000000000000000)⟩,(15495838321839759/15625000000000000),(1554251659698957/3906250000000000),(235422674407155289/1000000000000000000),(142074746190392753/1000000000000000000)⟩
theorem valid1061 : certificate1061.Valid := by decide +kernel
theorem sound1061 : certificate1061.Sound := rat_cut_bin_certificate_sound certificate1061 profilesValid1061 numericValid1061 valid1061

def retention1062 : RatCutRetentionCertificate := ⟨(53/1000),(213/4000),(7157516006735250449/16506479533787880736),(918692758622549089/250000000000000000),(11/10),(352537680746299211557/320000000000000000000),true,MergedCutProfiles.Batch177.profile7119,![MergedCutProfiles.Batch177.profile7119,MergedCutProfiles.Batch178.profile7120,MergedCutProfiles.Batch178.profile7121,MergedCutProfiles.Batch178.profile7122,MergedCutProfiles.Batch178.profile7123,MergedCutProfiles.Batch178.profile7124,MergedCutProfiles.Batch178.profile7125,MergedCutProfiles.Batch178.profile7126,MergedCutProfiles.Batch178.profile7127,MergedCutProfiles.Batch178.profile7128,MergedCutProfiles.Batch178.profile7129,MergedCutProfiles.Batch178.profile7130,MergedCutProfiles.Batch178.profile7131,MergedCutProfiles.Batch178.profile7132,MergedCutProfiles.Batch178.profile7133,MergedCutProfiles.Batch178.profile7134]⟩
theorem profilesValid1062 : retention1062.ProfilesValid := by
  change ∀ j : Fin 16, (retention1062.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch177.valid7119
  · exact MergedCutProfiles.Batch178.valid7120
  · exact MergedCutProfiles.Batch178.valid7121
  · exact MergedCutProfiles.Batch178.valid7122
  · exact MergedCutProfiles.Batch178.valid7123
  · exact MergedCutProfiles.Batch178.valid7124
  · exact MergedCutProfiles.Batch178.valid7125
  · exact MergedCutProfiles.Batch178.valid7126
  · exact MergedCutProfiles.Batch178.valid7127
  · exact MergedCutProfiles.Batch178.valid7128
  · exact MergedCutProfiles.Batch178.valid7129
  · exact MergedCutProfiles.Batch178.valid7130
  · exact MergedCutProfiles.Batch178.valid7131
  · exact MergedCutProfiles.Batch178.valid7132
  · exact MergedCutProfiles.Batch178.valid7133
  · exact MergedCutProfiles.Batch178.valid7134
theorem numericValid1062 : retention1062.NumericValid := by decide +kernel
def certificate1062 : RatCutBinCertificate := ⟨⟨retention1062,(2215121588008153677/1000000000000000000),(138194877202670159/1000000000000000000),(14013165961528612701/1000000000000000000),(57911559766397994477/250000000000000000),(1077647139553381971/1000000000000000000)⟩,(15495838321839759/15625000000000000),(461331820996434457/1000000000000000000),(181764293673237483/1000000000000000000),(71003907185801913/500000000000000000)⟩
theorem valid1062 : certificate1062.Valid := by decide +kernel
theorem sound1062 : certificate1062.Sound := rat_cut_bin_certificate_sound certificate1062 profilesValid1062 numericValid1062 valid1062

def retention1063 : RatCutRetentionCertificate := ⟨(53/1000),(213/4000),(1008158523744938023/2063309941723485092),(7157516006735250449/1000000000000000000),(21/20),(11553902365009996408358099369826923486919/11452025610776400718400000000000000000000),false,MergedCutProfiles.Batch178.profile7135,(fun _ => MergedCutProfiles.Batch178.profile7135)⟩
theorem profilesValid1063 : retention1063.ProfilesValid := by
  exact MergedCutProfiles.Batch178.valid7135
theorem numericValid1063 : retention1063.NumericValid := by decide +kernel
def certificate1063 : RatCutBinCertificate := ⟨⟨retention1063,(2215121588008153677/1000000000000000000),(138194877202670159/1000000000000000000),(14013165961528612701/1000000000000000000),(57911559766397994477/250000000000000000),(61622301576023959/62500000000000000)⟩,(15495838321839759/15625000000000000),(470384028969395863/1000000000000000000),(17484945003331797/100000000000000000),(144658069813117459/1000000000000000000)⟩
theorem valid1063 : certificate1063.Valid := by decide +kernel
theorem sound1063 : certificate1063.Sound := rat_cut_bin_certificate_sound certificate1063 profilesValid1063 numericValid1063 valid1063

def retention1064 : RatCutRetentionCertificate := ⟨(53/1000),(213/4000),(747943643688880929/1500589048526170976),(1008158523744938023/125000000000000000),(21/20),(801279851118865322480000392709920399799/806526818995950418400000000000000000000),false,MergedCutProfiles.Batch178.profile7136,(fun _ => MergedCutProfiles.Batch178.profile7136)⟩
theorem profilesValid1064 : retention1064.ProfilesValid := by
  exact MergedCutProfiles.Batch178.valid7136
theorem numericValid1064 : retention1064.NumericValid := by decide +kernel
def certificate1064 : RatCutBinCertificate := ⟨⟨retention1064,(2215121588008153677/1000000000000000000),(138194877202670159/1000000000000000000),(14013165961528612701/1000000000000000000),(57911559766397994477/250000000000000000),(970555437322074541/1000000000000000000)⟩,(15495838321839759/15625000000000000),(473764693154432247/1000000000000000000),(10769491761890609/62500000000000000),(142338471474289851/1000000000000000000)⟩
theorem valid1064 : certificate1064.Valid := by decide +kernel
theorem sound1064 : certificate1064.Sound := rat_cut_bin_certificate_sound certificate1064 profilesValid1064 numericValid1064 valid1064

def retention1065 : RatCutRetentionCertificate := ⟨(53/1000),(213/4000),(1/2),(8227380080577690219/1000000000000000000),(21/20),(13045118404300740370487864318939899739639/13163808128924304350400000000000000000000),false,MergedCutProfiles.Batch178.profile7137,(fun _ => MergedCutProfiles.Batch178.profile7137)⟩
theorem profilesValid1065 : retention1065.ProfilesValid := by
  exact MergedCutProfiles.Batch178.valid7137
theorem numericValid1065 : retention1065.NumericValid := by decide +kernel
def certificate1065 : RatCutBinCertificate := ⟨⟨retention1065,(2215121588008153677/1000000000000000000),(138194877202670159/1000000000000000000),(14013165961528612701/1000000000000000000),(57911559766397994477/250000000000000000),(378142474877433/390625000000000)⟩,(15495838321839759/15625000000000000),(474357339379011093/1000000000000000000),(171869508129234623/1000000000000000000),(35479425563610203/250000000000000000)⟩
theorem valid1065 : certificate1065.Valid := by decide +kernel
theorem sound1065 : certificate1065.Sound := rat_cut_bin_certificate_sound certificate1065 profilesValid1065 numericValid1065 valid1065

def retention1066 : RatCutRetentionCertificate := ⟨(53/1000),(213/4000),(1/2),64,1,(2553983369082114766078100910777197079/2560000000000000000000000000000000000),false,MergedCutProfiles.Batch178.profile7137,(fun _ => MergedCutProfiles.Batch178.profile7137)⟩
theorem profilesValid1066 : retention1066.ProfilesValid := by
  exact MergedCutProfiles.Batch178.valid7137
theorem numericValid1066 : retention1066.NumericValid := by decide +kernel
def certificate1066 : RatCutBinCertificate := ⟨⟨retention1066,(2215121588008153677/1000000000000000000),(138194877202670159/1000000000000000000),(14013165961528612701/1000000000000000000),(57911559766397994477/250000000000000000),(975804489588552069/1000000000000000000)⟩,(15495838321839759/15625000000000000),(221612987876984803/500000000000000000),(196131543311563397/1000000000000000000),(46734816793767939/250000000000000000)⟩
theorem valid1066 : certificate1066.Valid := by decide +kernel
theorem sound1066 : certificate1066.Sound := rat_cut_bin_certificate_sound certificate1066 profilesValid1066 numericValid1066 valid1066

def retention1067 : RatCutRetentionCertificate := ⟨(53/1000),(213/4000),(7536095138854764901/16506479533787880736),(929541625710708197/250000000000000000),(6/5),(401971705056969646481254450786962217431/371816650284283278800000000000000000000),false,MergedCutProfiles.Batch178.profile7138,(fun _ => MergedCutProfiles.Batch178.profile7138)⟩
theorem profilesValid1067 : retention1067.ProfilesValid := by
  exact MergedCutProfiles.Batch178.valid7138
theorem numericValid1067 : retention1067.NumericValid := by decide +kernel
def certificate1067 : RatCutBinCertificate := ⟨⟨retention1067,(2569472782008153677/1000000000000000000),(138194877202670159/1000000000000000000),(14013165961528612701/1000000000000000000),(57911559766397994477/250000000000000000),(1050690366464794521/1000000000000000000)⟩,(990409283933989647/1000000000000000000),(378410897135058443/1000000000000000000),(31732053489706671/125000000000000000),(18385511066745801/100000000000000000)⟩
theorem valid1067 : certificate1067.Valid := by decide +kernel
theorem sound1067 : certificate1067.Sound := rat_cut_bin_certificate_sound certificate1067 profilesValid1067 numericValid1067 valid1067

def certificates : List RatCutBinCertificate := [certificate1056,certificate1057,certificate1058,certificate1059,certificate1060,certificate1061,certificate1062,certificate1063,certificate1064,certificate1065,certificate1066,certificate1067]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound1056,List.forall_mem_cons.mpr ⟨sound1057,List.forall_mem_cons.mpr ⟨sound1058,List.forall_mem_cons.mpr ⟨sound1059,List.forall_mem_cons.mpr ⟨sound1060,List.forall_mem_cons.mpr ⟨sound1061,List.forall_mem_cons.mpr ⟨sound1062,List.forall_mem_cons.mpr ⟨sound1063,List.forall_mem_cons.mpr ⟨sound1064,List.forall_mem_cons.mpr ⟨sound1065,List.forall_mem_cons.mpr ⟨sound1066,List.forall_mem_cons.mpr ⟨sound1067,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch088
