import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch502
import Cycle12.MergedCutProfiles.Batch503
import Cycle12.MergedCutProfiles.Batch504

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch273

def retention3276 : RatCutRetentionCertificate := ⟨(53/1000),(107/2000),(403976114873331308/816433007188468595),(19800809473254156847/500000000000000000),1,(31855988301755895918756587554384169427/31681295157206650955200000000000000000),false,MergedCutProfiles.Batch502.profile20102,(fun _ => MergedCutProfiles.Batch502.profile20102)⟩
theorem profilesValid3276 : retention3276.ProfilesValid := by
  exact MergedCutProfiles.Batch502.valid20102
theorem numericValid3276 : retention3276.NumericValid := by decide +kernel
def certificate3276 : RatCutBinCertificate := ⟨⟨retention3276,(2127361553394259841/1000000000000000000),(17460968802135489/125000000000000000),(7008338157695654169/500000000000000000),(573859666037521547669/500000000000000000),(984313099176475963/1000000000000000000)⟩,(998399440572570273/1000000000000000000),(438984164206291169/1000000000000000000),(199603313466091479/1000000000000000000),(191395673481270863/1000000000000000000)⟩
theorem valid3276 : certificate3276.Valid := by decide +kernel
theorem sound3276 : certificate3276.Sound := rat_cut_bin_certificate_sound certificate3276 profilesValid3276 numericValid3276 valid3276

def retention3277 : RatCutRetentionCertificate := ⟨(53/1000),(107/2000),(10200396900551615527/20410825179711714875),(100994028718332827/2500000000000000),1,(160919269457032046692430962616690579079/161590445949332523200000000000000000000),false,MergedCutProfiles.Batch502.profile20103,(fun _ => MergedCutProfiles.Batch502.profile20103)⟩
theorem profilesValid3277 : retention3277.ProfilesValid := by
  exact MergedCutProfiles.Batch502.valid20103
theorem numericValid3277 : retention3277.NumericValid := by decide +kernel
def certificate3277 : RatCutBinCertificate := ⟨⟨retention3277,(2127361553394259841/1000000000000000000),(17460968802135489/125000000000000000),(7008338157695654169/500000000000000000),(573859666037521547669/500000000000000000),(243661364160206471/250000000000000000)⟩,(998399440572570273/1000000000000000000),(221577787010407597/500000000000000000),(39237766455760727/200000000000000000),(186406610901613877/1000000000000000000)⟩
theorem valid3277 : certificate3277.Valid := by decide +kernel
theorem sound3277 : certificate3277.Sound := rat_cut_bin_certificate_sound certificate3277 profilesValid3277 numericValid3277 valid3277

def retention3278 : RatCutRetentionCertificate := ⟨(53/1000),(107/2000),(1/2),(10200396900551615527/250000000000000000),1,(40614787448020603751663876004204023823/40801587602206462108000000000000000000),false,MergedCutProfiles.Batch502.profile20104,(fun _ => MergedCutProfiles.Batch502.profile20104)⟩
theorem profilesValid3278 : retention3278.ProfilesValid := by
  exact MergedCutProfiles.Batch502.valid20104
theorem numericValid3278 : retention3278.NumericValid := by decide +kernel
def certificate3278 : RatCutBinCertificate := ⟨⟨retention3278,(2127361553394259841/1000000000000000000),(17460968802135489/125000000000000000),(7008338157695654169/500000000000000000),(573859666037521547669/500000000000000000),(487110382856732571/500000000000000000)⟩,(998399440572570273/1000000000000000000),(443258607917216843/1000000000000000000),(196104992886531699/1000000000000000000),(186291150408515113/1000000000000000000)⟩
theorem valid3278 : certificate3278.Valid := by decide +kernel
theorem sound3278 : certificate3278.Sound := rat_cut_bin_certificate_sound certificate3278 profilesValid3278 numericValid3278 valid3278

def retention3279 : RatCutRetentionCertificate := ⟨(53/1000),(107/2000),(375264422576209289/816433007188468595),(989175396307718913/100000000000000000),1,(41673407451519847504038633379399962671/39567015852308756520000000000000000000),false,MergedCutProfiles.Batch502.profile20105,(fun _ => MergedCutProfiles.Batch502.profile20105)⟩
theorem profilesValid3279 : retention3279.ProfilesValid := by
  exact MergedCutProfiles.Batch502.valid20105
theorem numericValid3279 : retention3279.NumericValid := by decide +kernel
def certificate3279 : RatCutBinCertificate := ⟨⟨retention3279,(2220049333394259841/1000000000000000000),(17460968802135489/125000000000000000),(7008338157695654169/500000000000000000),(573859666037521547669/500000000000000000),(257777788151557513/250000000000000000)⟩,(249582421694463507/250000000000000000),(23836932070415287/200000000000000000),(78148450144585607/125000000000000000),(145689090444662431/250000000000000000)⟩
theorem valid3279 : certificate3279.Valid := by decide +kernel
theorem sound3279 : certificate3279.Sound := rat_cut_bin_certificate_sound certificate3279 profilesValid3279 numericValid3279 valid3279

def retention3280 : RatCutRetentionCertificate := ⟨(53/1000),(107/2000),(8127151927405954363/16328660143769371900),(375264422576209289/10000000000000000),1,(37503419777892109126081886940923129271/37526442257620928900000000000000000000),false,MergedCutProfiles.Batch502.profile20106,(fun _ => MergedCutProfiles.Batch502.profile20106)⟩
theorem profilesValid3280 : retention3280.ProfilesValid := by
  exact MergedCutProfiles.Batch502.valid20106
theorem numericValid3280 : retention3280.NumericValid := by decide +kernel
def certificate3280 : RatCutBinCertificate := ⟨⟨retention3280,(2220049333394259841/1000000000000000000),(17460968802135489/125000000000000000),(7008338157695654169/500000000000000000),(573859666037521547669/500000000000000000),(3817428920943867/3906250000000000)⟩,(249582421694463507/250000000000000000),(125752006305351409/1000000000000000000),(611706176614163849/1000000000000000000),(116327243454519413/200000000000000000)⟩
theorem valid3280 : certificate3280.Valid := by decide +kernel
theorem sound3280 : certificate3280.Sound := rat_cut_bin_certificate_sound certificate3280 profilesValid3280 numericValid3280 valid3280

def retention3281 : RatCutRetentionCertificate := ⟨(53/1000),(107/2000),(1/2),(8127151927405954363/200000000000000000),1,(40448699433441248108670206673851206029/40635759637029771815000000000000000000),false,MergedCutProfiles.Batch502.profile20104,(fun _ => MergedCutProfiles.Batch502.profile20104)⟩
theorem profilesValid3281 : retention3281.ProfilesValid := by
  exact MergedCutProfiles.Batch502.valid20104
theorem numericValid3281 : retention3281.NumericValid := by decide +kernel
def certificate3281 : RatCutBinCertificate := ⟨⟨retention3281,(2220049333394259841/1000000000000000000),(17460968802135489/125000000000000000),(7008338157695654169/500000000000000000),(573859666037521547669/500000000000000000),(243317992449607149/250000000000000000)⟩,(249582421694463507/250000000000000000),(31566878612065521/250000000000000000),(610660663958141417/1000000000000000000),(289726717743781347/500000000000000000)⟩
theorem valid3281 : certificate3281.Valid := by decide +kernel
theorem sound3281 : certificate3281.Sound := rat_cut_bin_certificate_sound certificate3281 profilesValid3281 numericValid3281 valid3281

def retention3282 : RatCutRetentionCertificate := ⟨(107/2000),(27/500),(823450421166994979/79903598409142039492),(203824361674998757/250000000000000000),(33/10),(5684571377138595219/2500000000000000000),true,MergedCutProfiles.Batch502.profile20107,![MergedCutProfiles.Batch502.profile20107,MergedCutProfiles.Batch502.profile20108,MergedCutProfiles.Batch502.profile20109,MergedCutProfiles.Batch502.profile20110,MergedCutProfiles.Batch502.profile20111,MergedCutProfiles.Batch502.profile20112,MergedCutProfiles.Batch502.profile20113,MergedCutProfiles.Batch502.profile20114,MergedCutProfiles.Batch502.profile20115,MergedCutProfiles.Batch502.profile20116,MergedCutProfiles.Batch502.profile20117,MergedCutProfiles.Batch502.profile20118,MergedCutProfiles.Batch502.profile20119,MergedCutProfiles.Batch503.profile20120,MergedCutProfiles.Batch503.profile20121,MergedCutProfiles.Batch503.profile20122]⟩
theorem profilesValid3282 : retention3282.ProfilesValid := by
  change ∀ j : Fin 16, (retention3282.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch502.valid20107
  · exact MergedCutProfiles.Batch502.valid20108
  · exact MergedCutProfiles.Batch502.valid20109
  · exact MergedCutProfiles.Batch502.valid20110
  · exact MergedCutProfiles.Batch502.valid20111
  · exact MergedCutProfiles.Batch502.valid20112
  · exact MergedCutProfiles.Batch502.valid20113
  · exact MergedCutProfiles.Batch502.valid20114
  · exact MergedCutProfiles.Batch502.valid20115
  · exact MergedCutProfiles.Batch502.valid20116
  · exact MergedCutProfiles.Batch502.valid20117
  · exact MergedCutProfiles.Batch502.valid20118
  · exact MergedCutProfiles.Batch502.valid20119
  · exact MergedCutProfiles.Batch503.valid20120
  · exact MergedCutProfiles.Batch503.valid20121
  · exact MergedCutProfiles.Batch503.valid20122
theorem numericValid3282 : retention3282.NumericValid := by decide +kernel
def certificate3282 : RatCutBinCertificate := ⟨⟨retention3282,(2126774859921381717/1000000000000000000),(142705547327693923/1000000000000000000),(7068853974728153609/500000000000000000),(1132973115748863439211/1000000000000000000),(1101491087502822411/500000000000000000)⟩,(998384627483786401/1000000000000000000),(48572784040217073/125000000000000000),(244108299567408769/1000000000000000000),(65156761048304099/500000000000000000)⟩
theorem valid3282 : certificate3282.Valid := by decide +kernel
theorem sound3282 : certificate3282.Sound := rat_cut_bin_certificate_sound certificate3282 profilesValid3282 numericValid3282 valid3282

def retention3283 : RatCutRetentionCertificate := ⟨(107/2000),(27/500),(253703415580478744/19975899602285509873),(823450421166994979/1000000000000000000),(33/10),(2899199950323976867743/1280000000000000000000),true,MergedCutProfiles.Batch503.profile20123,![MergedCutProfiles.Batch503.profile20123,MergedCutProfiles.Batch503.profile20124,MergedCutProfiles.Batch503.profile20125,MergedCutProfiles.Batch503.profile20126,MergedCutProfiles.Batch503.profile20127,MergedCutProfiles.Batch503.profile20128,MergedCutProfiles.Batch503.profile20129,MergedCutProfiles.Batch503.profile20130,MergedCutProfiles.Batch503.profile20131,MergedCutProfiles.Batch503.profile20132,MergedCutProfiles.Batch503.profile20133,MergedCutProfiles.Batch503.profile20134,MergedCutProfiles.Batch503.profile20135,MergedCutProfiles.Batch503.profile20136,MergedCutProfiles.Batch503.profile20137,MergedCutProfiles.Batch503.profile20138]⟩
theorem profilesValid3283 : retention3283.ProfilesValid := by
  change ∀ j : Fin 16, (retention3283.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch503.valid20123
  · exact MergedCutProfiles.Batch503.valid20124
  · exact MergedCutProfiles.Batch503.valid20125
  · exact MergedCutProfiles.Batch503.valid20126
  · exact MergedCutProfiles.Batch503.valid20127
  · exact MergedCutProfiles.Batch503.valid20128
  · exact MergedCutProfiles.Batch503.valid20129
  · exact MergedCutProfiles.Batch503.valid20130
  · exact MergedCutProfiles.Batch503.valid20131
  · exact MergedCutProfiles.Batch503.valid20132
  · exact MergedCutProfiles.Batch503.valid20133
  · exact MergedCutProfiles.Batch503.valid20134
  · exact MergedCutProfiles.Batch503.valid20135
  · exact MergedCutProfiles.Batch503.valid20136
  · exact MergedCutProfiles.Batch503.valid20137
  · exact MergedCutProfiles.Batch503.valid20138
theorem numericValid3283 : retention3283.NumericValid := by decide +kernel
def certificate3283 : RatCutBinCertificate := ⟨⟨retention3283,(2126774859921381717/1000000000000000000),(142705547327693923/1000000000000000000),(7068853974728153609/500000000000000000),(1132973115748863439211/1000000000000000000),(274269202272261579/125000000000000000)⟩,(998384627483786401/1000000000000000000),(388184983994269691/1000000000000000000),(24448401710343177/100000000000000000),(130350719926707837/1000000000000000000)⟩
theorem valid3283 : certificate3283.Valid := by decide +kernel
theorem sound3283 : certificate3283.Sound := rat_cut_bin_certificate_sound certificate3283 profilesValid3283 numericValid3283 valid3283

def retention3284 : RatCutRetentionCertificate := ⟨(107/2000),(27/500),(273981626250000000/19975899602285509873),(31712926947559843/31250000000000000),(11/4),(1794414335852447423/800000000000000000),true,MergedCutProfiles.Batch503.profile20139,![MergedCutProfiles.Batch503.profile20139,MergedCutProfiles.Batch503.profile20140,MergedCutProfiles.Batch502.profile20110,MergedCutProfiles.Batch503.profile20141,MergedCutProfiles.Batch503.profile20142,MergedCutProfiles.Batch503.profile20143,MergedCutProfiles.Batch503.profile20144,MergedCutProfiles.Batch503.profile20145,MergedCutProfiles.Batch503.profile20146,MergedCutProfiles.Batch503.profile20147,MergedCutProfiles.Batch503.profile20148,MergedCutProfiles.Batch503.profile20122,MergedCutProfiles.Batch503.profile20149,MergedCutProfiles.Batch503.profile20150,MergedCutProfiles.Batch503.profile20151,MergedCutProfiles.Batch503.profile20152]⟩
theorem profilesValid3284 : retention3284.ProfilesValid := by
  change ∀ j : Fin 16, (retention3284.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch503.valid20139
  · exact MergedCutProfiles.Batch503.valid20140
  · exact MergedCutProfiles.Batch502.valid20110
  · exact MergedCutProfiles.Batch503.valid20141
  · exact MergedCutProfiles.Batch503.valid20142
  · exact MergedCutProfiles.Batch503.valid20143
  · exact MergedCutProfiles.Batch503.valid20144
  · exact MergedCutProfiles.Batch503.valid20145
  · exact MergedCutProfiles.Batch503.valid20146
  · exact MergedCutProfiles.Batch503.valid20147
  · exact MergedCutProfiles.Batch503.valid20148
  · exact MergedCutProfiles.Batch503.valid20122
  · exact MergedCutProfiles.Batch503.valid20149
  · exact MergedCutProfiles.Batch503.valid20150
  · exact MergedCutProfiles.Batch503.valid20151
  · exact MergedCutProfiles.Batch503.valid20152
theorem numericValid3284 : retention3284.NumericValid := by decide +kernel
def certificate3284 : RatCutBinCertificate := ⟨⟨retention3284,(2126774859921381717/1000000000000000000),(142705547327693923/1000000000000000000),(7068853974728153609/500000000000000000),(1132973115748863439211/1000000000000000000),(545994843140624233/250000000000000000)⟩,(998384627483786401/1000000000000000000),(352846043014699579/1000000000000000000),(279580596777561267/1000000000000000000),(21564973867459061/125000000000000000)⟩
theorem valid3284 : certificate3284.Valid := by decide +kernel
theorem sound3284 : certificate3284.Sound := rat_cut_bin_certificate_sound certificate3284 profilesValid3284 numericValid3284 valid3284

def retention3285 : RatCutRetentionCertificate := ⟨(107/2000),(27/500),(1288544068853701659/79903598409142039492),(219185301/200000000),(13/5),(142642982047896837/64000000000000000),true,MergedCutProfiles.Batch503.profile20153,![MergedCutProfiles.Batch503.profile20153,MergedCutProfiles.Batch503.profile20154,MergedCutProfiles.Batch503.profile20155,MergedCutProfiles.Batch503.profile20156,MergedCutProfiles.Batch503.profile20157,MergedCutProfiles.Batch503.profile20158,MergedCutProfiles.Batch502.profile20117,MergedCutProfiles.Batch503.profile20159,MergedCutProfiles.Batch504.profile20160,MergedCutProfiles.Batch504.profile20161,MergedCutProfiles.Batch503.profile20136,MergedCutProfiles.Batch504.profile20162,MergedCutProfiles.Batch504.profile20163,MergedCutProfiles.Batch504.profile20164,MergedCutProfiles.Batch504.profile20165,MergedCutProfiles.Batch504.profile20166]⟩
theorem profilesValid3285 : retention3285.ProfilesValid := by
  change ∀ j : Fin 16, (retention3285.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch503.valid20153
  · exact MergedCutProfiles.Batch503.valid20154
  · exact MergedCutProfiles.Batch503.valid20155
  · exact MergedCutProfiles.Batch503.valid20156
  · exact MergedCutProfiles.Batch503.valid20157
  · exact MergedCutProfiles.Batch503.valid20158
  · exact MergedCutProfiles.Batch502.valid20117
  · exact MergedCutProfiles.Batch503.valid20159
  · exact MergedCutProfiles.Batch504.valid20160
  · exact MergedCutProfiles.Batch504.valid20161
  · exact MergedCutProfiles.Batch503.valid20136
  · exact MergedCutProfiles.Batch504.valid20162
  · exact MergedCutProfiles.Batch504.valid20163
  · exact MergedCutProfiles.Batch504.valid20164
  · exact MergedCutProfiles.Batch504.valid20165
  · exact MergedCutProfiles.Batch504.valid20166
theorem numericValid3285 : retention3285.NumericValid := by decide +kernel
def certificate3285 : RatCutBinCertificate := ⟨⟨retention3285,(2126774859921381717/1000000000000000000),(142705547327693923/1000000000000000000),(7068853974728153609/500000000000000000),(1132973115748863439211/1000000000000000000),(43459567670252293/20000000000000000)⟩,(998384627483786401/1000000000000000000),(342741659830891567/1000000000000000000),(29025087763631411/100000000000000000),(187211163749142613/1000000000000000000)⟩
theorem valid3285 : certificate3285.Valid := by decide +kernel
theorem sound3285 : certificate3285.Sound := rat_cut_bin_certificate_sound certificate3285 profilesValid3285 numericValid3285 valid3285

def retention3286 : RatCutRetentionCertificate := ⟨(107/2000),(27/500),(5240985758511525191/79903598409142039492),(1288544068853701659/1000000000000000000),(9/4),(516726771078035926599/256000000000000000000),true,MergedCutProfiles.Batch504.profile20167,![MergedCutProfiles.Batch504.profile20167,MergedCutProfiles.Batch504.profile20168,MergedCutProfiles.Batch504.profile20169,MergedCutProfiles.Batch504.profile20170,MergedCutProfiles.Batch504.profile20171,MergedCutProfiles.Batch504.profile20172,MergedCutProfiles.Batch504.profile20173,MergedCutProfiles.Batch504.profile20174,MergedCutProfiles.Batch504.profile20175,MergedCutProfiles.Batch504.profile20176,MergedCutProfiles.Batch504.profile20177,MergedCutProfiles.Batch504.profile20178,MergedCutProfiles.Batch504.profile20179,MergedCutProfiles.Batch504.profile20180,MergedCutProfiles.Batch504.profile20181,MergedCutProfiles.Batch504.profile20182]⟩
theorem profilesValid3286 : retention3286.ProfilesValid := by
  change ∀ j : Fin 16, (retention3286.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch504.valid20167
  · exact MergedCutProfiles.Batch504.valid20168
  · exact MergedCutProfiles.Batch504.valid20169
  · exact MergedCutProfiles.Batch504.valid20170
  · exact MergedCutProfiles.Batch504.valid20171
  · exact MergedCutProfiles.Batch504.valid20172
  · exact MergedCutProfiles.Batch504.valid20173
  · exact MergedCutProfiles.Batch504.valid20174
  · exact MergedCutProfiles.Batch504.valid20175
  · exact MergedCutProfiles.Batch504.valid20176
  · exact MergedCutProfiles.Batch504.valid20177
  · exact MergedCutProfiles.Batch504.valid20178
  · exact MergedCutProfiles.Batch504.valid20179
  · exact MergedCutProfiles.Batch504.valid20180
  · exact MergedCutProfiles.Batch504.valid20181
  · exact MergedCutProfiles.Batch504.valid20182
theorem numericValid3286 : retention3286.NumericValid := by decide +kernel
def certificate3286 : RatCutBinCertificate := ⟨⟨retention3286,(2126774859921381717/1000000000000000000),(142705547327693923/1000000000000000000),(7068853974728153609/500000000000000000),(1132973115748863439211/1000000000000000000),(1970159765165248339/1000000000000000000)⟩,(998384627483786401/1000000000000000000),(176748842949177149/500000000000000000),(13945123246976527/50000000000000000),(2925196316819453/15625000000000000)⟩
theorem valid3286 : certificate3286.Valid := by decide +kernel
theorem sound3286 : certificate3286.Sound := rat_cut_bin_certificate_sound certificate3286 profilesValid3286 numericValid3286 valid3286

def retention3287 : RatCutRetentionCertificate := ⟨(107/2000),(27/500),(8013883352561813395/19975899602285509873),(5240985758511525191/1000000000000000000),(23/20),(10015361464371044200920392495250437193391/8385577213618440305600000000000000000000),false,MergedCutProfiles.Batch504.profile20183,(fun _ => MergedCutProfiles.Batch504.profile20183)⟩
theorem profilesValid3287 : retention3287.ProfilesValid := by
  exact MergedCutProfiles.Batch504.valid20183
theorem numericValid3287 : retention3287.NumericValid := by decide +kernel
def certificate3287 : RatCutBinCertificate := ⟨⟨retention3287,(2126774859921381717/1000000000000000000),(142705547327693923/1000000000000000000),(7068853974728153609/500000000000000000),(1132973115748863439211/1000000000000000000),(1169667394225209343/1000000000000000000)⟩,(998384627483786401/1000000000000000000),(418154268906850891/1000000000000000000),(27156778249578039/125000000000000000),(188731910714834503/1000000000000000000)⟩
theorem valid3287 : certificate3287.Valid := by decide +kernel
theorem sound3287 : certificate3287.Sound := rat_cut_bin_certificate_sound certificate3287 profilesValid3287 numericValid3287 valid3287

def certificates : List RatCutBinCertificate := [certificate3276,certificate3277,certificate3278,certificate3279,certificate3280,certificate3281,certificate3282,certificate3283,certificate3284,certificate3285,certificate3286,certificate3287]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound3276,List.forall_mem_cons.mpr ⟨sound3277,List.forall_mem_cons.mpr ⟨sound3278,List.forall_mem_cons.mpr ⟨sound3279,List.forall_mem_cons.mpr ⟨sound3280,List.forall_mem_cons.mpr ⟨sound3281,List.forall_mem_cons.mpr ⟨sound3282,List.forall_mem_cons.mpr ⟨sound3283,List.forall_mem_cons.mpr ⟨sound3284,List.forall_mem_cons.mpr ⟨sound3285,List.forall_mem_cons.mpr ⟨sound3286,List.forall_mem_cons.mpr ⟨sound3287,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch273
