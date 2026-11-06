import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch353
import Cycle12.MergedCutProfiles.Batch354
import Cycle12.MergedCutProfiles.Batch355
import Cycle12.MergedCutProfiles.Batch356
import Cycle12.MergedCutProfiles.Batch474
import Cycle12.MergedCutProfiles.Batch475
import Cycle12.MergedCutProfiles.Batch476

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch257

def retention3084 : RatCutRetentionCertificate := ⟨(1/25),(41/1000),(614850909496975236/74574689523806123209),(56247297/50000000),(13/5),(36296176609825953587/16000000000000000000),true,MergedCutProfiles.Batch475.profile19002,![MergedCutProfiles.Batch475.profile19002,MergedCutProfiles.Batch475.profile19003,MergedCutProfiles.Batch475.profile19004,MergedCutProfiles.Batch474.profile18982,MergedCutProfiles.Batch354.profile14163,MergedCutProfiles.Batch475.profile19005,MergedCutProfiles.Batch474.profile18985,MergedCutProfiles.Batch354.profile14177,MergedCutProfiles.Batch475.profile19006,MergedCutProfiles.Batch474.profile18998,MergedCutProfiles.Batch353.profile14122,MergedCutProfiles.Batch475.profile19007,MergedCutProfiles.Batch475.profile19008,MergedCutProfiles.Batch475.profile19009,MergedCutProfiles.Batch353.profile14154,MergedCutProfiles.Batch354.profile14178]⟩
theorem profilesValid3084 : retention3084.ProfilesValid := by
  change ∀ j : Fin 16, (retention3084.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch475.valid19002
  · exact MergedCutProfiles.Batch475.valid19003
  · exact MergedCutProfiles.Batch475.valid19004
  · exact MergedCutProfiles.Batch474.valid18982
  · exact MergedCutProfiles.Batch354.valid14163
  · exact MergedCutProfiles.Batch475.valid19005
  · exact MergedCutProfiles.Batch474.valid18985
  · exact MergedCutProfiles.Batch354.valid14177
  · exact MergedCutProfiles.Batch475.valid19006
  · exact MergedCutProfiles.Batch474.valid18998
  · exact MergedCutProfiles.Batch353.valid14122
  · exact MergedCutProfiles.Batch475.valid19007
  · exact MergedCutProfiles.Batch475.valid19008
  · exact MergedCutProfiles.Batch475.valid19009
  · exact MergedCutProfiles.Batch353.valid14154
  · exact MergedCutProfiles.Batch354.valid14178
theorem numericValid3084 : retention3084.NumericValid := by decide +kernel
def certificate3084 : RatCutBinCertificate := ⟨⟨retention3084,(997483386825986613/500000000000000000),(77009395027439323/1000000000000000000),(2270527801094209419/200000000000000000),(1702396676814811822403/1000000000000000000),(139582851762383329/62500000000000000)⟩,(998913549265470927/1000000000000000000),(374815750823041/976562500000000),(124323578052668661/500000000000000000),(82444315133399527/500000000000000000)⟩
theorem valid3084 : certificate3084.Valid := by decide +kernel
theorem sound3084 : certificate3084.Sound := rat_cut_bin_certificate_sound certificate3084 profilesValid3084 numericValid3084 valid3084

def retention3085 : RatCutRetentionCertificate := ⟨(1/25),(41/1000),(4308170792399226425/149149379047612246418),(153712727374243809/125000000000000000),(49/20),(21583355625619084983/10000000000000000000),true,MergedCutProfiles.Batch475.profile19010,![MergedCutProfiles.Batch475.profile19010,MergedCutProfiles.Batch474.profile18985,MergedCutProfiles.Batch475.profile19011,MergedCutProfiles.Batch353.profile14124,MergedCutProfiles.Batch475.profile19012,MergedCutProfiles.Batch475.profile19013,MergedCutProfiles.Batch353.profile14144,MergedCutProfiles.Batch475.profile19014,MergedCutProfiles.Batch475.profile19015,MergedCutProfiles.Batch475.profile19016,MergedCutProfiles.Batch475.profile19017,MergedCutProfiles.Batch475.profile19018,MergedCutProfiles.Batch475.profile19019,MergedCutProfiles.Batch475.profile19020,MergedCutProfiles.Batch475.profile19021,MergedCutProfiles.Batch475.profile19022]⟩
theorem profilesValid3085 : retention3085.ProfilesValid := by
  change ∀ j : Fin 16, (retention3085.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch475.valid19010
  · exact MergedCutProfiles.Batch474.valid18985
  · exact MergedCutProfiles.Batch475.valid19011
  · exact MergedCutProfiles.Batch353.valid14124
  · exact MergedCutProfiles.Batch475.valid19012
  · exact MergedCutProfiles.Batch475.valid19013
  · exact MergedCutProfiles.Batch353.valid14144
  · exact MergedCutProfiles.Batch475.valid19014
  · exact MergedCutProfiles.Batch475.valid19015
  · exact MergedCutProfiles.Batch475.valid19016
  · exact MergedCutProfiles.Batch475.valid19017
  · exact MergedCutProfiles.Batch475.valid19018
  · exact MergedCutProfiles.Batch475.valid19019
  · exact MergedCutProfiles.Batch475.valid19020
  · exact MergedCutProfiles.Batch475.valid19021
  · exact MergedCutProfiles.Batch475.valid19022
theorem numericValid3085 : retention3085.NumericValid := by decide +kernel
def certificate3085 : RatCutBinCertificate := ⟨⟨retention3085,(997483386825986613/500000000000000000),(77009395027439323/1000000000000000000),(2270527801094209419/200000000000000000),(1702396676814811822403/1000000000000000000),(531295023775848959/250000000000000000)⟩,(998913549265470927/1000000000000000000),(38750394874115287/100000000000000000),(30641127631754589/125000000000000000),(41222501472647911/250000000000000000)⟩
theorem valid3085 : certificate3085.Valid := by decide +kernel
theorem sound3085 : certificate3085.Sound := rat_cut_bin_certificate_sound certificate3085 profilesValid3085 numericValid3085 valid3085

def retention3086 : RatCutRetentionCertificate := ⟨(1/25),(41/1000),(53407282323291428515/149149379047612246418),(172326831695969057/40000000000000000),(5/4),(355448390156860682651303863369082131151/275722930713550491200000000000000000000),false,MergedCutProfiles.Batch475.profile19023,(fun _ => MergedCutProfiles.Batch475.profile19023)⟩
theorem profilesValid3086 : retention3086.ProfilesValid := by
  exact MergedCutProfiles.Batch475.valid19023
theorem numericValid3086 : retention3086.NumericValid := by decide +kernel
def certificate3086 : RatCutBinCertificate := ⟨⟨retention3086,(997483386825986613/500000000000000000),(77009395027439323/1000000000000000000),(2270527801094209419/200000000000000000),(1702396676814811822403/1000000000000000000),(636117344117574671/500000000000000000)⟩,(998913549265470927/1000000000000000000),(44427708425152969/100000000000000000),(24409692379295859/125000000000000000),(6678421046291867/40000000000000000)⟩
theorem valid3086 : certificate3086.Valid := by decide +kernel
theorem sound3086 : certificate3086.Sound := rat_cut_bin_certificate_sound certificate3086 profilesValid3086 numericValid3086 valid3086

def retention3087 : RatCutRetentionCertificate := ⟨(1/25),(41/1000),(32000000000000000000/74574689523806123209),(10681456464658285703/200000000000000000),1,(3800853101920400400069790322234019099/3337955145205714282187500000000000000),false,MergedCutProfiles.Batch475.profile19024,(fun _ => MergedCutProfiles.Batch475.profile19024)⟩
theorem profilesValid3087 : retention3087.ProfilesValid := by
  exact MergedCutProfiles.Batch475.valid19024
theorem numericValid3087 : retention3087.NumericValid := by decide +kernel
def certificate3087 : RatCutBinCertificate := ⟨⟨retention3087,(997483386825986613/500000000000000000),(77009395027439323/1000000000000000000),(2270527801094209419/200000000000000000),(1702396676814811822403/1000000000000000000),(56257222651653113/50000000000000000)⟩,(998913549265470927/1000000000000000000),(418055227502910143/1000000000000000000),(2716757375395893/12500000000000000),(23923110149807731/100000000000000000)⟩
theorem valid3087 : certificate3087.Valid := by decide +kernel
theorem sound3087 : certificate3087.Sound := rat_cut_bin_certificate_sound certificate3087 profilesValid3087 numericValid3087 valid3087

def retention3088 : RatCutRetentionCertificate := ⟨(1/25),(41/1000),(1/2),64,1,(255384100590301156902854846823122473239/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch354.profile14195,(fun _ => MergedCutProfiles.Batch354.profile14195)⟩
theorem profilesValid3088 : retention3088.ProfilesValid := by
  exact MergedCutProfiles.Batch354.valid14195
theorem numericValid3088 : retention3088.NumericValid := by decide +kernel
def certificate3088 : RatCutBinCertificate := ⟨⟨retention3088,(997483386825986613/500000000000000000),(77009395027439323/1000000000000000000),(2270527801094209419/200000000000000000),(1702396676814811822403/1000000000000000000),(492030746346978301/500000000000000000)⟩,(998913549265470927/1000000000000000000),(476591164135926511/1000000000000000000),(85104397393497953/500000000000000000),(41194670882304841/250000000000000000)⟩
theorem valid3088 : certificate3088.Valid := by decide +kernel
theorem sound3088 : certificate3088.Sound := rat_cut_bin_certificate_sound certificate3088 profilesValid3088 numericValid3088 valid3088

def retention3089 : RatCutRetentionCertificate := ⟨(1/25),(41/1000),(32000000000000000000/74574689523806123209),(9920695515166500201/1000000000000000000),1,(153190038136869284881226086182536683/137787437710645836125000000000000000),false,MergedCutProfiles.Batch475.profile19024,(fun _ => MergedCutProfiles.Batch475.profile19024)⟩
theorem profilesValid3089 : retention3089.ProfilesValid := by
  exact MergedCutProfiles.Batch475.valid19024
theorem numericValid3089 : retention3089.NumericValid := by decide +kernel
def certificate3089 : RatCutBinCertificate := ⟨⟨retention3089,(1067197046825986613/500000000000000000),(77009395027439323/1000000000000000000),(2270527801094209419/200000000000000000),(1702396676814811822403/1000000000000000000),(274326683322180401/250000000000000000)⟩,(998837610771514549/1000000000000000000),(4662606284897819/40000000000000000),(25226008717718047/40000000000000000),(311168614842446147/500000000000000000)⟩
theorem valid3089 : certificate3089.Valid := by decide +kernel
theorem sound3089 : certificate3089.Sound := rat_cut_bin_certificate_sound certificate3089 profilesValid3089 numericValid3089 valid3089

def retention3090 : RatCutRetentionCertificate := ⟨(1/25),(41/1000),(1/2),64,1,(255384100590301156902854846823122473239/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch354.profile14195,(fun _ => MergedCutProfiles.Batch354.profile14195)⟩
theorem profilesValid3090 : retention3090.ProfilesValid := by
  exact MergedCutProfiles.Batch354.valid14195
theorem numericValid3090 : retention3090.NumericValid := by decide +kernel
def certificate3090 : RatCutBinCertificate := ⟨⟨retention3090,(1067197046825986613/500000000000000000),(77009395027439323/1000000000000000000),(2270527801094209419/200000000000000000),(1702396676814811822403/1000000000000000000),(983115701926937787/1000000000000000000)⟩,(998837610771514549/1000000000000000000),(1626305677025273/12500000000000000),(75366993940737671/125000000000000000),(583103853101806373/1000000000000000000)⟩
theorem valid3090 : certificate3090.Valid := by decide +kernel
theorem sound3090 : certificate3090.Sound := rat_cut_bin_certificate_sound certificate3090 profilesValid3090 numericValid3090 valid3090

def retention3091 : RatCutRetentionCertificate := ⟨(41/1000),(21/500),(360401253601907419/70681137771170960324),(356832924358324177/500000000000000000),(19/5),(92688922055656590337/40000000000000000000),true,MergedCutProfiles.Batch475.profile19025,![MergedCutProfiles.Batch475.profile19025,MergedCutProfiles.Batch475.profile19026,MergedCutProfiles.Batch475.profile19027,MergedCutProfiles.Batch475.profile19028,MergedCutProfiles.Batch475.profile19029,MergedCutProfiles.Batch475.profile19030,MergedCutProfiles.Batch475.profile19031,MergedCutProfiles.Batch475.profile19032,MergedCutProfiles.Batch475.profile19033,MergedCutProfiles.Batch475.profile19034,MergedCutProfiles.Batch475.profile19035,MergedCutProfiles.Batch475.profile19036,MergedCutProfiles.Batch475.profile19037,MergedCutProfiles.Batch475.profile19038,MergedCutProfiles.Batch475.profile19039,MergedCutProfiles.Batch355.profile14218]⟩
theorem profilesValid3091 : retention3091.ProfilesValid := by
  change ∀ j : Fin 16, (retention3091.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch475.valid19025
  · exact MergedCutProfiles.Batch475.valid19026
  · exact MergedCutProfiles.Batch475.valid19027
  · exact MergedCutProfiles.Batch475.valid19028
  · exact MergedCutProfiles.Batch475.valid19029
  · exact MergedCutProfiles.Batch475.valid19030
  · exact MergedCutProfiles.Batch475.valid19031
  · exact MergedCutProfiles.Batch475.valid19032
  · exact MergedCutProfiles.Batch475.valid19033
  · exact MergedCutProfiles.Batch475.valid19034
  · exact MergedCutProfiles.Batch475.valid19035
  · exact MergedCutProfiles.Batch475.valid19036
  · exact MergedCutProfiles.Batch475.valid19037
  · exact MergedCutProfiles.Batch475.valid19038
  · exact MergedCutProfiles.Batch475.valid19039
  · exact MergedCutProfiles.Batch355.valid14218
theorem numericValid3091 : retention3091.NumericValid := by decide +kernel
def certificate3091 : RatCutBinCertificate := ⟨⟨retention3091,(100210803454060891/50000000000000000),(81190354661587239/1000000000000000000),(11528825716416863327/1000000000000000000),(1638610208469183050743/1000000000000000000),(45271743365338939/20000000000000000)⟩,(998870965459877583/1000000000000000000),(236971982664320067/500000000000000000),(86088989289411189/500000000000000000),(16796081577252561/200000000000000000)⟩
theorem valid3091 : certificate3091.Valid := by decide +kernel
theorem sound3091 : certificate3091.Sound := rat_cut_bin_certificate_sound certificate3091 profilesValid3091 numericValid3091 valid3091

def retention3092 : RatCutRetentionCertificate := ⟨(41/1000),(21/500),(476194920843005959/70681137771170960324),(360401253601907419/500000000000000000),(19/5),(1476597808641438206903/640000000000000000000),true,MergedCutProfiles.Batch476.profile19040,![MergedCutProfiles.Batch476.profile19040,MergedCutProfiles.Batch476.profile19041,MergedCutProfiles.Batch476.profile19042,MergedCutProfiles.Batch354.profile14199,MergedCutProfiles.Batch356.profile14264,MergedCutProfiles.Batch476.profile19043,MergedCutProfiles.Batch476.profile19044,MergedCutProfiles.Batch476.profile19045,MergedCutProfiles.Batch475.profile19036,MergedCutProfiles.Batch356.profile14265,MergedCutProfiles.Batch476.profile19046,MergedCutProfiles.Batch476.profile19047,MergedCutProfiles.Batch476.profile19048,MergedCutProfiles.Batch476.profile19049,MergedCutProfiles.Batch356.profile14266,MergedCutProfiles.Batch476.profile19050]⟩
theorem profilesValid3092 : retention3092.ProfilesValid := by
  change ∀ j : Fin 16, (retention3092.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch476.valid19040
  · exact MergedCutProfiles.Batch476.valid19041
  · exact MergedCutProfiles.Batch476.valid19042
  · exact MergedCutProfiles.Batch354.valid14199
  · exact MergedCutProfiles.Batch356.valid14264
  · exact MergedCutProfiles.Batch476.valid19043
  · exact MergedCutProfiles.Batch476.valid19044
  · exact MergedCutProfiles.Batch476.valid19045
  · exact MergedCutProfiles.Batch475.valid19036
  · exact MergedCutProfiles.Batch356.valid14265
  · exact MergedCutProfiles.Batch476.valid19046
  · exact MergedCutProfiles.Batch476.valid19047
  · exact MergedCutProfiles.Batch476.valid19048
  · exact MergedCutProfiles.Batch476.valid19049
  · exact MergedCutProfiles.Batch356.valid14266
  · exact MergedCutProfiles.Batch476.valid19050
theorem numericValid3092 : retention3092.NumericValid := by decide +kernel
def certificate3092 : RatCutBinCertificate := ⟨⟨retention3092,(100210803454060891/50000000000000000),(81190354661587239/1000000000000000000),(11528825716416863327/1000000000000000000),(1638610208469183050743/1000000000000000000),(563387050645029337/250000000000000000)⟩,(998870965459877583/1000000000000000000),(236681571940698473/500000000000000000),(43153002963057617/250000000000000000),(5252196305817461/62500000000000000)⟩
theorem valid3092 : certificate3092.Valid := by decide +kernel
theorem sound3092 : certificate3092.Sound := rat_cut_bin_certificate_sound certificate3092 profilesValid3092 numericValid3092 valid3092

def retention3093 : RatCutRetentionCertificate := ⟨(41/1000),(21/500),(142279627875000000/17670284442792740081),(476194920843005959/500000000000000000),(59/20),(1456464015768329178047/640000000000000000000),true,MergedCutProfiles.Batch476.profile19051,![MergedCutProfiles.Batch476.profile19051,MergedCutProfiles.Batch476.profile19052,MergedCutProfiles.Batch476.profile19053,MergedCutProfiles.Batch476.profile19054,MergedCutProfiles.Batch476.profile19043,MergedCutProfiles.Batch476.profile19055,MergedCutProfiles.Batch475.profile19035,MergedCutProfiles.Batch476.profile19056,MergedCutProfiles.Batch476.profile19057,MergedCutProfiles.Batch476.profile19047,MergedCutProfiles.Batch476.profile19058,MergedCutProfiles.Batch356.profile14254,MergedCutProfiles.Batch476.profile19059,MergedCutProfiles.Batch476.profile19060,MergedCutProfiles.Batch476.profile19061,MergedCutProfiles.Batch355.profile14234]⟩
theorem profilesValid3093 : retention3093.ProfilesValid := by
  change ∀ j : Fin 16, (retention3093.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch476.valid19051
  · exact MergedCutProfiles.Batch476.valid19052
  · exact MergedCutProfiles.Batch476.valid19053
  · exact MergedCutProfiles.Batch476.valid19054
  · exact MergedCutProfiles.Batch476.valid19043
  · exact MergedCutProfiles.Batch476.valid19055
  · exact MergedCutProfiles.Batch475.valid19035
  · exact MergedCutProfiles.Batch476.valid19056
  · exact MergedCutProfiles.Batch476.valid19057
  · exact MergedCutProfiles.Batch476.valid19047
  · exact MergedCutProfiles.Batch476.valid19058
  · exact MergedCutProfiles.Batch356.valid14254
  · exact MergedCutProfiles.Batch476.valid19059
  · exact MergedCutProfiles.Batch476.valid19060
  · exact MergedCutProfiles.Batch476.valid19061
  · exact MergedCutProfiles.Batch355.valid14234
theorem numericValid3093 : retention3093.NumericValid := by decide +kernel
def certificate3093 : RatCutBinCertificate := ⟨⟨retention3093,(100210803454060891/50000000000000000),(81190354661587239/1000000000000000000),(11528825716416863327/1000000000000000000),(1638610208469183050743/1000000000000000000),(558521667029642953/250000000000000000)⟩,(998870965459877583/1000000000000000000),(205726859359500311/500000000000000000),(8926010600325183/40000000000000000),(26587907916722899/200000000000000000)⟩
theorem valid3093 : certificate3093.Valid := by decide +kernel
theorem sound3093 : certificate3093.Sound := rat_cut_bin_certificate_sound certificate3093 profilesValid3093 numericValid3093 valid3093

def retention3094 : RatCutRetentionCertificate := ⟨(41/1000),(21/500),(1646229244879562819/141362275542341920648),(1138237023/1000000000),(51/20),(8964932226688855347/4000000000000000000),true,MergedCutProfiles.Batch476.profile19062,![MergedCutProfiles.Batch476.profile19062,MergedCutProfiles.Batch476.profile19063,MergedCutProfiles.Batch476.profile19064,MergedCutProfiles.Batch476.profile19065,MergedCutProfiles.Batch356.profile14252,MergedCutProfiles.Batch476.profile19066,MergedCutProfiles.Batch355.profile14218,MergedCutProfiles.Batch476.profile19067,MergedCutProfiles.Batch476.profile19059,MergedCutProfiles.Batch356.profile14255,MergedCutProfiles.Batch355.profile14234,MergedCutProfiles.Batch476.profile19068,MergedCutProfiles.Batch355.profile14208,MergedCutProfiles.Batch355.profile14223,MergedCutProfiles.Batch356.profile14258,MergedCutProfiles.Batch476.profile19069]⟩
theorem profilesValid3094 : retention3094.ProfilesValid := by
  change ∀ j : Fin 16, (retention3094.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch476.valid19062
  · exact MergedCutProfiles.Batch476.valid19063
  · exact MergedCutProfiles.Batch476.valid19064
  · exact MergedCutProfiles.Batch476.valid19065
  · exact MergedCutProfiles.Batch356.valid14252
  · exact MergedCutProfiles.Batch476.valid19066
  · exact MergedCutProfiles.Batch355.valid14218
  · exact MergedCutProfiles.Batch476.valid19067
  · exact MergedCutProfiles.Batch476.valid19059
  · exact MergedCutProfiles.Batch356.valid14255
  · exact MergedCutProfiles.Batch355.valid14234
  · exact MergedCutProfiles.Batch476.valid19068
  · exact MergedCutProfiles.Batch355.valid14208
  · exact MergedCutProfiles.Batch355.valid14223
  · exact MergedCutProfiles.Batch356.valid14258
  · exact MergedCutProfiles.Batch476.valid19069
theorem numericValid3094 : retention3094.NumericValid := by decide +kernel
def certificate3094 : RatCutBinCertificate := ⟨⟨retention3094,(100210803454060891/50000000000000000),(81190354661587239/1000000000000000000),(11528825716416863327/1000000000000000000),(1638610208469183050743/1000000000000000000),(1102620299665395041/500000000000000000)⟩,(998870965459877583/1000000000000000000),(382839672275402139/1000000000000000000),(249578785769374803/1000000000000000000),(83036468480600013/500000000000000000)⟩
theorem valid3094 : certificate3094.Valid := by decide +kernel
theorem sound3094 : certificate3094.Sound := rat_cut_bin_certificate_sound certificate3094 profilesValid3094 numericValid3094 valid3094

def retention3095 : RatCutRetentionCertificate := ⟨(41/1000),(21/500),(17061340540673542135/141362275542341920648),(1646229244879562819/1000000000000000000),2,(1518626906829147167326817467883122561/823114622439781409500000000000000000),false,MergedCutProfiles.Batch476.profile19070,(fun _ => MergedCutProfiles.Batch476.profile19070)⟩
theorem profilesValid3095 : retention3095.ProfilesValid := by
  exact MergedCutProfiles.Batch476.valid19070
theorem numericValid3095 : retention3095.NumericValid := by decide +kernel
def certificate3095 : RatCutBinCertificate := ⟨⟨retention3095,(100210803454060891/50000000000000000),(81190354661587239/1000000000000000000),(11528825716416863327/1000000000000000000),(1638610208469183050743/1000000000000000000),(363349380262193139/200000000000000000)⟩,(998870965459877583/1000000000000000000),(399450777526162699/1000000000000000000),(233985965231398229/1000000000000000000),(41593010900690973/250000000000000000)⟩
theorem valid3095 : certificate3095.Valid := by decide +kernel
theorem sound3095 : certificate3095.Sound := rat_cut_bin_certificate_sound certificate3095 profilesValid3095 numericValid3095 valid3095

def certificates : List RatCutBinCertificate := [certificate3084,certificate3085,certificate3086,certificate3087,certificate3088,certificate3089,certificate3090,certificate3091,certificate3092,certificate3093,certificate3094,certificate3095]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound3084,List.forall_mem_cons.mpr ⟨sound3085,List.forall_mem_cons.mpr ⟨sound3086,List.forall_mem_cons.mpr ⟨sound3087,List.forall_mem_cons.mpr ⟨sound3088,List.forall_mem_cons.mpr ⟨sound3089,List.forall_mem_cons.mpr ⟨sound3090,List.forall_mem_cons.mpr ⟨sound3091,List.forall_mem_cons.mpr ⟨sound3092,List.forall_mem_cons.mpr ⟨sound3093,List.forall_mem_cons.mpr ⟨sound3094,List.forall_mem_cons.mpr ⟨sound3095,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch257
