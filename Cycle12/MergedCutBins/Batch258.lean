import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch357
import Cycle12.MergedCutProfiles.Batch358
import Cycle12.MergedCutProfiles.Batch359
import Cycle12.MergedCutProfiles.Batch476
import Cycle12.MergedCutProfiles.Batch477
import Cycle12.MergedCutProfiles.Batch478

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch258

def retention3096 : RatCutRetentionCertificate := ⟨(41/1000),(21/500),(8000000000000000000/17670284442792740081),(3412268108134708427/200000000000000000),1,(4332009897063718027550021337088634883/4014433068393774620000000000000000000),false,MergedCutProfiles.Batch476.profile19071,(fun _ => MergedCutProfiles.Batch476.profile19071)⟩
theorem profilesValid3096 : retention3096.ProfilesValid := by
  exact MergedCutProfiles.Batch476.valid19071
theorem numericValid3096 : retention3096.NumericValid := by decide +kernel
def certificate3096 : RatCutBinCertificate := ⟨⟨retention3096,(100210803454060891/50000000000000000),(81190354661587239/1000000000000000000),(11528825716416863327/1000000000000000000),(1638610208469183050743/1000000000000000000),(1064994272428104233/1000000000000000000)⟩,(998870965459877583/1000000000000000000),(228027487480016873/500000000000000000),(92938459413228313/500000000000000000),(93054945597530277/500000000000000000)⟩
theorem valid3096 : certificate3096.Valid := by decide +kernel
theorem sound3096 : certificate3096.Sound := rat_cut_bin_certificate_sound certificate3096 profilesValid3096 numericValid3096 valid3096

def retention3097 : RatCutRetentionCertificate := ⟨(41/1000),(21/500),(1/2),64,1,(63846252801030998518146708381256195671/64000000000000000000000000000000000000),false,MergedCutProfiles.Batch357.profile14283,(fun _ => MergedCutProfiles.Batch357.profile14283)⟩
theorem profilesValid3097 : retention3097.ProfilesValid := by
  exact MergedCutProfiles.Batch357.valid14283
theorem numericValid3097 : retention3097.NumericValid := by decide +kernel
def certificate3097 : RatCutBinCertificate := ⟨⟨retention3097,(100210803454060891/50000000000000000),(81190354661587239/1000000000000000000),(11528825716416863327/1000000000000000000),(1638610208469183050743/1000000000000000000),(491741620440678449/500000000000000000)⟩,(998870965459877583/1000000000000000000),(474738953272946343/1000000000000000000),(8579252884895661/50000000000000000),(41501940174007583/250000000000000000)⟩
theorem valid3097 : certificate3097.Valid := by decide +kernel
theorem sound3097 : certificate3097.Sound := rat_cut_bin_certificate_sound certificate3097 profilesValid3097 numericValid3097 valid3097

def retention3098 : RatCutRetentionCertificate := ⟨(41/1000),(21/500),(8000000000000000000/17670284442792740081),(9894663936877018079/1000000000000000000),1,(42204423300809845413445564149920697939/39578655747508072316000000000000000000),false,MergedCutProfiles.Batch476.profile19071,(fun _ => MergedCutProfiles.Batch476.profile19071)⟩
theorem profilesValid3098 : retention3098.ProfilesValid := by
  exact MergedCutProfiles.Batch476.valid19071
theorem numericValid3098 : retention3098.NumericValid := by decide +kernel
def certificate3098 : RatCutBinCertificate := ⟨⟨retention3098,(107119168204060891/50000000000000000),(81190354661587239/1000000000000000000),(11528825716416863327/1000000000000000000),(1638610208469183050743/1000000000000000000),(262813867484293529/250000000000000000)⟩,(99879312387446673/100000000000000000),(121848908379980549/1000000000000000000),(154920481902678819/250000000000000000),(117626515798443391/200000000000000000)⟩
theorem valid3098 : certificate3098.Valid := by decide +kernel
theorem sound3098 : certificate3098.Sound := rat_cut_bin_certificate_sound certificate3098 profilesValid3098 numericValid3098 valid3098

def retention3099 : RatCutRetentionCertificate := ⟨(41/1000),(21/500),(1/2),64,1,(63846252801030998518146708381256195671/64000000000000000000000000000000000000),false,MergedCutProfiles.Batch357.profile14283,(fun _ => MergedCutProfiles.Batch357.profile14283)⟩
theorem profilesValid3099 : retention3099.ProfilesValid := by
  exact MergedCutProfiles.Batch357.valid14283
theorem numericValid3099 : retention3099.NumericValid := by decide +kernel
def certificate3099 : RatCutBinCertificate := ⟨⟨retention3099,(107119168204060891/50000000000000000),(81190354661587239/1000000000000000000),(11528825716416863327/1000000000000000000),(1638610208469183050743/1000000000000000000),(491255106868334229/500000000000000000)⟩,(99879312387446673/100000000000000000),(130374554533292473/1000000000000000000),(75299491522289947/125000000000000000),(29110102060321483/50000000000000000)⟩
theorem valid3099 : certificate3099.Valid := by decide +kernel
theorem sound3099 : certificate3099.Sound := rat_cut_bin_certificate_sound certificate3099 profilesValid3099 numericValid3099 valid3099

def retention3100 : RatCutRetentionCertificate := ⟨(21/500),(43/1000),(727737404782681589/134129227617246420223),(360266041971624549/500000000000000000),(15/4),(1849719837554717793/800000000000000000),true,MergedCutProfiles.Batch476.profile19072,![MergedCutProfiles.Batch476.profile19072,MergedCutProfiles.Batch476.profile19073,MergedCutProfiles.Batch476.profile19074,MergedCutProfiles.Batch476.profile19075,MergedCutProfiles.Batch476.profile19076,MergedCutProfiles.Batch476.profile19077,MergedCutProfiles.Batch476.profile19078,MergedCutProfiles.Batch476.profile19079,MergedCutProfiles.Batch477.profile19080,MergedCutProfiles.Batch477.profile19081,MergedCutProfiles.Batch477.profile19082,MergedCutProfiles.Batch477.profile19083,MergedCutProfiles.Batch477.profile19084,MergedCutProfiles.Batch477.profile19085,MergedCutProfiles.Batch477.profile19086,MergedCutProfiles.Batch357.profile14307]⟩
theorem profilesValid3100 : retention3100.ProfilesValid := by
  change ∀ j : Fin 16, (retention3100.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch476.valid19072
  · exact MergedCutProfiles.Batch476.valid19073
  · exact MergedCutProfiles.Batch476.valid19074
  · exact MergedCutProfiles.Batch476.valid19075
  · exact MergedCutProfiles.Batch476.valid19076
  · exact MergedCutProfiles.Batch476.valid19077
  · exact MergedCutProfiles.Batch476.valid19078
  · exact MergedCutProfiles.Batch476.valid19079
  · exact MergedCutProfiles.Batch477.valid19080
  · exact MergedCutProfiles.Batch477.valid19081
  · exact MergedCutProfiles.Batch477.valid19082
  · exact MergedCutProfiles.Batch477.valid19083
  · exact MergedCutProfiles.Batch477.valid19084
  · exact MergedCutProfiles.Batch477.valid19085
  · exact MergedCutProfiles.Batch477.valid19086
  · exact MergedCutProfiles.Batch357.valid14307
theorem numericValid3100 : retention3100.NumericValid := by decide +kernel
def certificate3100 : RatCutBinCertificate := ⟨⟨retention3100,(1005606824798281483/500000000000000000),(21376650541548341/250000000000000000),(2341848866977126349/200000000000000000),(1542141089801017007/976562500000000),(2257072964029854371/1000000000000000000)⟩,(249707419898170091/250000000000000000),(234937621102681077/500000000000000000),(8761672639206443/50000000000000000),(86137542869538339/1000000000000000000)⟩
theorem valid3100 : certificate3100.Valid := by decide +kernel
theorem sound3100 : certificate3100.Sound := rat_cut_bin_certificate_sound certificate3100 profilesValid3100 numericValid3100 valid3100

def retention3101 : RatCutRetentionCertificate := ⟨(21/500),(43/1000),(961552859213333109/134129227617246420223),(727737404782681589/1000000000000000000),(15/4),(589344982695986115553/256000000000000000000),true,MergedCutProfiles.Batch477.profile19087,![MergedCutProfiles.Batch477.profile19087,MergedCutProfiles.Batch477.profile19088,MergedCutProfiles.Batch476.profile19075,MergedCutProfiles.Batch477.profile19089,MergedCutProfiles.Batch477.profile19090,MergedCutProfiles.Batch476.profile19079,MergedCutProfiles.Batch358.profile14332,MergedCutProfiles.Batch477.profile19091,MergedCutProfiles.Batch477.profile19083,MergedCutProfiles.Batch477.profile19092,MergedCutProfiles.Batch358.profile14320,MergedCutProfiles.Batch357.profile14307,MergedCutProfiles.Batch477.profile19093,MergedCutProfiles.Batch358.profile14334,MergedCutProfiles.Batch358.profile14346,MergedCutProfiles.Batch477.profile19094]⟩
theorem profilesValid3101 : retention3101.ProfilesValid := by
  change ∀ j : Fin 16, (retention3101.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch477.valid19087
  · exact MergedCutProfiles.Batch477.valid19088
  · exact MergedCutProfiles.Batch476.valid19075
  · exact MergedCutProfiles.Batch477.valid19089
  · exact MergedCutProfiles.Batch477.valid19090
  · exact MergedCutProfiles.Batch476.valid19079
  · exact MergedCutProfiles.Batch358.valid14332
  · exact MergedCutProfiles.Batch477.valid19091
  · exact MergedCutProfiles.Batch477.valid19083
  · exact MergedCutProfiles.Batch477.valid19092
  · exact MergedCutProfiles.Batch358.valid14320
  · exact MergedCutProfiles.Batch357.valid14307
  · exact MergedCutProfiles.Batch477.valid19093
  · exact MergedCutProfiles.Batch358.valid14334
  · exact MergedCutProfiles.Batch358.valid14346
  · exact MergedCutProfiles.Batch477.valid19094
theorem numericValid3101 : retention3101.NumericValid := by decide +kernel
def certificate3101 : RatCutBinCertificate := ⟨⟨retention3101,(1005606824798281483/500000000000000000),(21376650541548341/250000000000000000),(2341848866977126349/200000000000000000),(1542141089801017007/976562500000000),(2247052016670380829/1000000000000000000)⟩,(249707419898170091/250000000000000000),(469324232438189377/1000000000000000000),(4391248609497891/25000000000000000),(86183529410364971/1000000000000000000)⟩
theorem valid3101 : certificate3101.Valid := by decide +kernel
theorem sound3101 : certificate3101.Sound := rat_cut_bin_certificate_sound certificate3101 profilesValid3101 numericValid3101 valid3101

def retention3102 : RatCutRetentionCertificate := ⟨(21/500),(43/1000),(1122961200000000000/134129227617246420223),(961552859213333109/1000000000000000000),(59/20),(2915753022457293531717/1280000000000000000000),true,MergedCutProfiles.Batch477.profile19095,![MergedCutProfiles.Batch477.profile19095,MergedCutProfiles.Batch477.profile19096,MergedCutProfiles.Batch358.profile14331,MergedCutProfiles.Batch477.profile19097,MergedCutProfiles.Batch477.profile19098,MergedCutProfiles.Batch358.profile14332,MergedCutProfiles.Batch357.profile14319,MergedCutProfiles.Batch477.profile19099,MergedCutProfiles.Batch358.profile14333,MergedCutProfiles.Batch477.profile19100,MergedCutProfiles.Batch477.profile19101,MergedCutProfiles.Batch358.profile14334,MergedCutProfiles.Batch477.profile19102,MergedCutProfiles.Batch357.profile14294,MergedCutProfiles.Batch358.profile14335,MergedCutProfiles.Batch477.profile19103]⟩
theorem profilesValid3102 : retention3102.ProfilesValid := by
  change ∀ j : Fin 16, (retention3102.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch477.valid19095
  · exact MergedCutProfiles.Batch477.valid19096
  · exact MergedCutProfiles.Batch358.valid14331
  · exact MergedCutProfiles.Batch477.valid19097
  · exact MergedCutProfiles.Batch477.valid19098
  · exact MergedCutProfiles.Batch358.valid14332
  · exact MergedCutProfiles.Batch357.valid14319
  · exact MergedCutProfiles.Batch477.valid19099
  · exact MergedCutProfiles.Batch358.valid14333
  · exact MergedCutProfiles.Batch477.valid19100
  · exact MergedCutProfiles.Batch477.valid19101
  · exact MergedCutProfiles.Batch358.valid14334
  · exact MergedCutProfiles.Batch477.valid19102
  · exact MergedCutProfiles.Batch357.valid14294
  · exact MergedCutProfiles.Batch358.valid14335
  · exact MergedCutProfiles.Batch477.valid19103
theorem numericValid3102 : retention3102.NumericValid := by decide +kernel
def certificate3102 : RatCutBinCertificate := ⟨⟨retention3102,(1005606824798281483/500000000000000000),(21376650541548341/250000000000000000),(2341848866977126349/200000000000000000),(1542141089801017007/976562500000000),(2234604981431198703/1000000000000000000)⟩,(249707419898170091/250000000000000000),(20361369017837761/50000000000000000),(226925151026367561/1000000000000000000),(27096164272936753/200000000000000000)⟩
theorem valid3102 : certificate3102.Valid := by decide +kernel
theorem sound3102 : certificate3102.Sound := rat_cut_bin_certificate_sound certificate3102 profilesValid3102 numericValid3102 valid3102

def retention3103 : RatCutRetentionCertificate := ⟨(21/500),(43/1000),(1335298922097199649/134129227617246420223),(2807403/2500000),(13/5),(18065058966049052997/8000000000000000000),true,MergedCutProfiles.Batch477.profile19104,![MergedCutProfiles.Batch477.profile19104,MergedCutProfiles.Batch477.profile19105,MergedCutProfiles.Batch477.profile19106,MergedCutProfiles.Batch477.profile19107,MergedCutProfiles.Batch358.profile14332,MergedCutProfiles.Batch477.profile19082,MergedCutProfiles.Batch477.profile19084,MergedCutProfiles.Batch477.profile19108,MergedCutProfiles.Batch477.profile19109,MergedCutProfiles.Batch477.profile19110,MergedCutProfiles.Batch477.profile19111,MergedCutProfiles.Batch477.profile19112,MergedCutProfiles.Batch477.profile19113,MergedCutProfiles.Batch477.profile19114,MergedCutProfiles.Batch477.profile19115,MergedCutProfiles.Batch477.profile19116]⟩
theorem profilesValid3103 : retention3103.ProfilesValid := by
  change ∀ j : Fin 16, (retention3103.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch477.valid19104
  · exact MergedCutProfiles.Batch477.valid19105
  · exact MergedCutProfiles.Batch477.valid19106
  · exact MergedCutProfiles.Batch477.valid19107
  · exact MergedCutProfiles.Batch358.valid14332
  · exact MergedCutProfiles.Batch477.valid19082
  · exact MergedCutProfiles.Batch477.valid19084
  · exact MergedCutProfiles.Batch477.valid19108
  · exact MergedCutProfiles.Batch477.valid19109
  · exact MergedCutProfiles.Batch477.valid19110
  · exact MergedCutProfiles.Batch477.valid19111
  · exact MergedCutProfiles.Batch477.valid19112
  · exact MergedCutProfiles.Batch477.valid19113
  · exact MergedCutProfiles.Batch477.valid19114
  · exact MergedCutProfiles.Batch477.valid19115
  · exact MergedCutProfiles.Batch477.valid19116
theorem numericValid3103 : retention3103.NumericValid := by decide +kernel
def certificate3103 : RatCutBinCertificate := ⟨⟨retention3103,(1005606824798281483/500000000000000000),(21376650541548341/250000000000000000),(2341848866977126349/200000000000000000),(1542141089801017007/976562500000000),(2219945823661359973/1000000000000000000)⟩,(249707419898170091/250000000000000000),(92962839377383/244140625000000),(251565831515557427/1000000000000000000),(165967809298278933/1000000000000000000)⟩
theorem valid3103 : certificate3103.Valid := by decide +kernel
theorem sound3103 : certificate3103.Sound := rat_cut_bin_certificate_sound certificate3103 profilesValid3103 numericValid3103 valid3103

def retention3104 : RatCutRetentionCertificate := ⟨(21/500),(43/1000),(7693789220359963004/134129227617246420223),(1335298922097199649/1000000000000000000),(9/4),(521960920226425661829/256000000000000000000),true,MergedCutProfiles.Batch477.profile19091,![MergedCutProfiles.Batch477.profile19091,MergedCutProfiles.Batch477.profile19094,MergedCutProfiles.Batch357.profile14311,MergedCutProfiles.Batch477.profile19117,MergedCutProfiles.Batch477.profile19118,MergedCutProfiles.Batch477.profile19119,MergedCutProfiles.Batch358.profile14345,MergedCutProfiles.Batch478.profile19120,MergedCutProfiles.Batch478.profile19121,MergedCutProfiles.Batch478.profile19122,MergedCutProfiles.Batch478.profile19123,MergedCutProfiles.Batch478.profile19124,MergedCutProfiles.Batch478.profile19125,MergedCutProfiles.Batch478.profile19126,MergedCutProfiles.Batch478.profile19127,MergedCutProfiles.Batch478.profile19128]⟩
theorem profilesValid3104 : retention3104.ProfilesValid := by
  change ∀ j : Fin 16, (retention3104.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch477.valid19091
  · exact MergedCutProfiles.Batch477.valid19094
  · exact MergedCutProfiles.Batch357.valid14311
  · exact MergedCutProfiles.Batch477.valid19117
  · exact MergedCutProfiles.Batch477.valid19118
  · exact MergedCutProfiles.Batch477.valid19119
  · exact MergedCutProfiles.Batch358.valid14345
  · exact MergedCutProfiles.Batch478.valid19120
  · exact MergedCutProfiles.Batch478.valid19121
  · exact MergedCutProfiles.Batch478.valid19122
  · exact MergedCutProfiles.Batch478.valid19123
  · exact MergedCutProfiles.Batch478.valid19124
  · exact MergedCutProfiles.Batch478.valid19125
  · exact MergedCutProfiles.Batch478.valid19126
  · exact MergedCutProfiles.Batch478.valid19127
  · exact MergedCutProfiles.Batch478.valid19128
theorem numericValid3104 : retention3104.NumericValid := by decide +kernel
def certificate3104 : RatCutBinCertificate := ⟨⟨retention3104,(1005606824798281483/500000000000000000),(21376650541548341/250000000000000000),(2341848866977126349/200000000000000000),(1542141089801017007/976562500000000),(1002931905772952729/500000000000000000)⟩,(249707419898170091/250000000000000000),(195431748796290937/500000000000000000),(30244847293378489/125000000000000000),(166121673363437461/1000000000000000000)⟩
theorem valid3104 : certificate3104.Valid := by decide +kernel
theorem sound3104 : certificate3104.Sound := rat_cut_bin_certificate_sound certificate3104 profilesValid3104 numericValid3104 valid3104

def retention3105 : RatCutRetentionCertificate := ⟨(21/500),(43/1000),(57419286059986091214/134129227617246420223),(1923447305089990751/250000000000000000),(21/20),(216971860522078529412715643139881816451/192344730508999075100000000000000000000),false,MergedCutProfiles.Batch478.profile19129,(fun _ => MergedCutProfiles.Batch478.profile19129)⟩
theorem profilesValid3105 : retention3105.ProfilesValid := by
  exact MergedCutProfiles.Batch478.valid19129
theorem numericValid3105 : retention3105.NumericValid := by decide +kernel
def certificate3105 : RatCutBinCertificate := ⟨⟨retention3105,(1005606824798281483/500000000000000000),(21376650541548341/250000000000000000),(2341848866977126349/200000000000000000),(1542141089801017007/976562500000000),(44504604355400699/40000000000000000)⟩,(249707419898170091/250000000000000000),(115981377982451653/250000000000000000),(179765009949462251/1000000000000000000),(21023386125647061/125000000000000000)⟩
theorem valid3105 : certificate3105.Valid := by decide +kernel
theorem sound3105 : certificate3105.Sound := rat_cut_bin_certificate_sound certificate3105 profilesValid3105 numericValid3105 valid3105

def retention3106 : RatCutRetentionCertificate := ⟨(21/500),(43/1000),(64000000000000000000/134129227617246420223),(28709643029993045607/500000000000000000),1,(239468885282482245278341834125248333903/229677144239944364856000000000000000000),false,MergedCutProfiles.Batch478.profile19130,(fun _ => MergedCutProfiles.Batch478.profile19130)⟩
theorem profilesValid3106 : retention3106.ProfilesValid := by
  exact MergedCutProfiles.Batch478.valid19130
theorem numericValid3106 : retention3106.NumericValid := by decide +kernel
def certificate3106 : RatCutBinCertificate := ⟨⟨retention3106,(1005606824798281483/500000000000000000),(21376650541548341/250000000000000000),(2341848866977126349/200000000000000000),(1542141089801017007/976562500000000),(1027945756475176767/1000000000000000000)⟩,(249707419898170091/250000000000000000),(113687577804057211/250000000000000000),(186903122915687179/1000000000000000000),(47131030060065743/250000000000000000)⟩
theorem valid3106 : certificate3106.Valid := by decide +kernel
theorem sound3106 : certificate3106.Sound := rat_cut_bin_certificate_sound certificate3106 profilesValid3106 numericValid3106 valid3106

def retention3107 : RatCutRetentionCertificate := ⟨(21/500),(43/1000),(1/2),64,1,(63846487671256044251940764516727514191/64000000000000000000000000000000000000),false,MergedCutProfiles.Batch359.profile14365,(fun _ => MergedCutProfiles.Batch359.profile14365)⟩
theorem profilesValid3107 : retention3107.ProfilesValid := by
  exact MergedCutProfiles.Batch359.valid14365
theorem numericValid3107 : retention3107.NumericValid := by decide +kernel
def certificate3107 : RatCutBinCertificate := ⟨⟨retention3107,(1005606824798281483/500000000000000000),(21376650541548341/250000000000000000),(2341848866977126349/200000000000000000),(1542141089801017007/976562500000000),(39316579852563859/40000000000000000)⟩,(249707419898170091/250000000000000000),(237397900284952333/500000000000000000),(171542710658745823/1000000000000000000),(41466334363795153/250000000000000000)⟩
theorem valid3107 : certificate3107.Valid := by decide +kernel
theorem sound3107 : certificate3107.Sound := rat_cut_bin_certificate_sound certificate3107 profilesValid3107 numericValid3107 valid3107

def certificates : List RatCutBinCertificate := [certificate3096,certificate3097,certificate3098,certificate3099,certificate3100,certificate3101,certificate3102,certificate3103,certificate3104,certificate3105,certificate3106,certificate3107]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound3096,List.forall_mem_cons.mpr ⟨sound3097,List.forall_mem_cons.mpr ⟨sound3098,List.forall_mem_cons.mpr ⟨sound3099,List.forall_mem_cons.mpr ⟨sound3100,List.forall_mem_cons.mpr ⟨sound3101,List.forall_mem_cons.mpr ⟨sound3102,List.forall_mem_cons.mpr ⟨sound3103,List.forall_mem_cons.mpr ⟨sound3104,List.forall_mem_cons.mpr ⟨sound3105,List.forall_mem_cons.mpr ⟨sound3106,List.forall_mem_cons.mpr ⟨sound3107,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch258
