import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch357
import Cycle12.MergedCutProfiles.Batch358
import Cycle12.MergedCutProfiles.Batch359
import Cycle12.MergedCutProfiles.Batch476
import Cycle12.MergedCutProfiles.Batch477
import Cycle12.MergedCutProfiles.Batch478
import Cycle12.MergedCutProfiles.Batch479
import Cycle12.MergedCutProfiles.Batch604
import Cycle12.MergedCutProfiles.Batch605

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch333

def retention3996 : RatCutRetentionCertificate := ⟨(41/1000),(21/500),(1/2),64,1,(63846252801030998518146708381256195671/64000000000000000000000000000000000000),false,MergedCutProfiles.Batch357.profile14283,(fun _ => MergedCutProfiles.Batch357.profile14283)⟩
theorem profilesValid3996 : retention3996.ProfilesValid := by
  exact MergedCutProfiles.Batch357.valid14283
theorem numericValid3996 : retention3996.NumericValid := by decide +kernel
def certificate3996 : RatCutBinCertificate := ⟨⟨retention3996,(376815787954060891/200000000000000000),(81190354661587239/1000000000000000000),(11528872124124012319/1000000000000000000),(6554467217879598236817/1000000000000000000),(246082338447549853/250000000000000000)⟩,(99973468084633257/100000000000000000),(27172825548716809/50000000000000000),(31285164852091873/250000000000000000),(3790040800602187/31250000000000000)⟩
theorem valid3996 : certificate3996.Valid := by decide +kernel
theorem sound3996 : certificate3996.Sound := rat_cut_bin_certificate_sound certificate3996 profilesValid3996 numericValid3996 valid3996

def retention3997 : RatCutRetentionCertificate := ⟨(41/1000),(21/500),(32000000000000000000/282724551084683841297),(6016102838994017583/250000000000000000),1,(35358107220826325907777657412924609507/19251529084780856265600000000000000000),false,MergedCutProfiles.Batch604.profile24181,(fun _ => MergedCutProfiles.Batch604.profile24181)⟩
theorem profilesValid3997 : retention3997.ProfilesValid := by
  exact MergedCutProfiles.Batch604.valid24181
theorem numericValid3997 : retention3997.NumericValid := by decide +kernel
def certificate3997 : RatCutBinCertificate := ⟨⟨retention3997,(367155344554060891/200000000000000000),(81190354661587239/1000000000000000000),(11528872124124012319/1000000000000000000),(6554467217879598236817/1000000000000000000),(911855355906578811/500000000000000000)⟩,(99974148299219027/100000000000000000),(32252049526385753/1000000000000000000),(167546685999592433/200000000000000000),(1419781247053027147/1000000000000000000)⟩
theorem valid3997 : certificate3997.Valid := by decide +kernel
theorem sound3997 : certificate3997.Sound := rat_cut_bin_certificate_sound certificate3997 profilesValid3997 numericValid3997 valid3997

def retention3998 : RatCutRetentionCertificate := ⟨(41/1000),(21/500),(1/2),64,1,(63846252801030998518146708381256195671/64000000000000000000000000000000000000),false,MergedCutProfiles.Batch357.profile14283,(fun _ => MergedCutProfiles.Batch357.profile14283)⟩
theorem profilesValid3998 : retention3998.ProfilesValid := by
  exact MergedCutProfiles.Batch357.valid14283
theorem numericValid3998 : retention3998.NumericValid := by decide +kernel
def certificate3998 : RatCutBinCertificate := ⟨⟨retention3998,(367155344554060891/200000000000000000),(81190354661587239/1000000000000000000),(11528872124124012319/1000000000000000000),(6554467217879598236817/1000000000000000000),(123083689372818759/125000000000000000)⟩,(99974148299219027/100000000000000000),(59734161872819361/1000000000000000000),(381377376943770583/500000000000000000),(739487922287016699/1000000000000000000)⟩
theorem valid3998 : certificate3998.Valid := by decide +kernel
theorem sound3998 : certificate3998.Sound := rat_cut_bin_certificate_sound certificate3998 profilesValid3998 numericValid3998 valid3998

def retention3999 : RatCutRetentionCertificate := ⟨(21/500),(43/1000),(612525484401360333/536516910468985680892),(118902240102913679/200000000000000000),4,(214574449692204064433781711725722527/95121792082330943200000000000000000),true,MergedCutProfiles.Batch604.profile24182,![MergedCutProfiles.Batch604.profile24182,MergedCutProfiles.Batch604.profile24183,MergedCutProfiles.Batch604.profile24184,MergedCutProfiles.Batch604.profile24185,MergedCutProfiles.Batch604.profile24186,MergedCutProfiles.Batch604.profile24187,MergedCutProfiles.Batch604.profile24188,MergedCutProfiles.Batch604.profile24189,MergedCutProfiles.Batch477.profile19104,MergedCutProfiles.Batch604.profile24190,MergedCutProfiles.Batch604.profile24191,MergedCutProfiles.Batch604.profile24192,MergedCutProfiles.Batch357.profile14287,MergedCutProfiles.Batch604.profile24193,MergedCutProfiles.Batch357.profile14303,MergedCutProfiles.Batch604.profile24194]⟩
theorem profilesValid3999 : retention3999.ProfilesValid := by
  change ∀ j : Fin 16, (retention3999.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch604.valid24182
  · exact MergedCutProfiles.Batch604.valid24183
  · exact MergedCutProfiles.Batch604.valid24184
  · exact MergedCutProfiles.Batch604.valid24185
  · exact MergedCutProfiles.Batch604.valid24186
  · exact MergedCutProfiles.Batch604.valid24187
  · exact MergedCutProfiles.Batch604.valid24188
  · exact MergedCutProfiles.Batch604.valid24189
  · exact MergedCutProfiles.Batch477.valid19104
  · exact MergedCutProfiles.Batch604.valid24190
  · exact MergedCutProfiles.Batch604.valid24191
  · exact MergedCutProfiles.Batch604.valid24192
  · exact MergedCutProfiles.Batch357.valid14287
  · exact MergedCutProfiles.Batch604.valid24193
  · exact MergedCutProfiles.Batch357.valid14303
  · exact MergedCutProfiles.Batch604.valid24194
theorem numericValid3999 : retention3999.NumericValid := by decide +kernel
def certificate3999 : RatCutBinCertificate := ⟨⟨retention3999,(945455743074570371/500000000000000000),(21376650541548341/250000000000000000),(2341859175842730431/200000000000000000),(3158318854834120979897/500000000000000000),(275069119276902011/125000000000000000)⟩,(999724943860244807/1000000000000000000),(697353961823983673/1000000000000000000),(25638161075565433/500000000000000000),(22901585292739343/1000000000000000000)⟩
theorem valid3999 : certificate3999.Valid := by decide +kernel
theorem sound3999 : certificate3999.Sound := rat_cut_bin_certificate_sound certificate3999 profilesValid3999 numericValid3999 valid3999

def retention4000 : RatCutRetentionCertificate := ⟨(21/500),(43/1000),(40277999750000000/19161318231035202889),(612525484401360333/1000000000000000000),4,(583184814240381788877/256000000000000000000),true,MergedCutProfiles.Batch604.profile24195,![MergedCutProfiles.Batch604.profile24195,MergedCutProfiles.Batch604.profile24196,MergedCutProfiles.Batch604.profile24197,MergedCutProfiles.Batch477.profile19095,MergedCutProfiles.Batch604.profile24198,MergedCutProfiles.Batch604.profile24191,MergedCutProfiles.Batch357.profile14287,MergedCutProfiles.Batch477.profile19096,MergedCutProfiles.Batch604.profile24199,MergedCutProfiles.Batch605.profile24200,MergedCutProfiles.Batch605.profile24201,MergedCutProfiles.Batch358.profile14331,MergedCutProfiles.Batch476.profile19076,MergedCutProfiles.Batch357.profile14288,MergedCutProfiles.Batch605.profile24202,MergedCutProfiles.Batch477.profile19097]⟩
theorem profilesValid4000 : retention4000.ProfilesValid := by
  change ∀ j : Fin 16, (retention4000.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch604.valid24195
  · exact MergedCutProfiles.Batch604.valid24196
  · exact MergedCutProfiles.Batch604.valid24197
  · exact MergedCutProfiles.Batch477.valid19095
  · exact MergedCutProfiles.Batch604.valid24198
  · exact MergedCutProfiles.Batch604.valid24191
  · exact MergedCutProfiles.Batch357.valid14287
  · exact MergedCutProfiles.Batch477.valid19096
  · exact MergedCutProfiles.Batch604.valid24199
  · exact MergedCutProfiles.Batch605.valid24200
  · exact MergedCutProfiles.Batch605.valid24201
  · exact MergedCutProfiles.Batch358.valid14331
  · exact MergedCutProfiles.Batch476.valid19076
  · exact MergedCutProfiles.Batch357.valid14288
  · exact MergedCutProfiles.Batch605.valid24202
  · exact MergedCutProfiles.Batch477.valid19097
theorem numericValid4000 : retention4000.NumericValid := by decide +kernel
def certificate4000 : RatCutBinCertificate := ⟨⟨retention4000,(945455743074570371/500000000000000000),(21376650541548341/250000000000000000),(2341859175842730431/200000000000000000),(3158318854834120979897/500000000000000000),(111141609697500253/50000000000000000)⟩,(999724943860244807/1000000000000000000),(13540128150121487/20000000000000000),(58910628431990491/1000000000000000000),(213406996372213/8000000000000000)⟩
theorem valid4000 : certificate4000.Valid := by decide +kernel
theorem sound4000 : certificate4000.Sound := rat_cut_bin_certificate_sound certificate4000 profilesValid4000 numericValid4000 valid4000

def retention4001 : RatCutRetentionCertificate := ⟨(21/500),(43/1000),(462100736793514429/134129227617246420223),(1127783993/1000000000),(11/4),(20171829972641861140628218668713/8604309028625488281250000000000),true,MergedCutProfiles.Batch605.profile24203,![MergedCutProfiles.Batch605.profile24203,MergedCutProfiles.Batch604.profile24187,MergedCutProfiles.Batch604.profile24198,MergedCutProfiles.Batch605.profile24204,MergedCutProfiles.Batch357.profile14303,MergedCutProfiles.Batch605.profile24205,MergedCutProfiles.Batch605.profile24206,MergedCutProfiles.Batch605.profile24207,MergedCutProfiles.Batch605.profile24202,MergedCutProfiles.Batch357.profile14304,MergedCutProfiles.Batch476.profile19078,MergedCutProfiles.Batch477.profile19098,MergedCutProfiles.Batch605.profile24208,MergedCutProfiles.Batch605.profile24209,MergedCutProfiles.Batch357.profile14305,MergedCutProfiles.Batch605.profile24210]⟩
theorem profilesValid4001 : retention4001.ProfilesValid := by
  change ∀ j : Fin 16, (retention4001.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch605.valid24203
  · exact MergedCutProfiles.Batch604.valid24187
  · exact MergedCutProfiles.Batch604.valid24198
  · exact MergedCutProfiles.Batch605.valid24204
  · exact MergedCutProfiles.Batch357.valid14303
  · exact MergedCutProfiles.Batch605.valid24205
  · exact MergedCutProfiles.Batch605.valid24206
  · exact MergedCutProfiles.Batch605.valid24207
  · exact MergedCutProfiles.Batch605.valid24202
  · exact MergedCutProfiles.Batch357.valid14304
  · exact MergedCutProfiles.Batch476.valid19078
  · exact MergedCutProfiles.Batch477.valid19098
  · exact MergedCutProfiles.Batch605.valid24208
  · exact MergedCutProfiles.Batch605.valid24209
  · exact MergedCutProfiles.Batch357.valid14305
  · exact MergedCutProfiles.Batch605.valid24210
theorem numericValid4001 : retention4001.NumericValid := by decide +kernel
def certificate4001 : RatCutBinCertificate := ⟨⟨retention4001,(945455743074570371/500000000000000000),(21376650541548341/250000000000000000),(2341859175842730431/200000000000000000),(3158318854834120979897/500000000000000000),(2306413991977356891/1000000000000000000)⟩,(999724943860244807/1000000000000000000),(458359544850552511/1000000000000000000),(184073334208948423/1000000000000000000),(15185119074038421/125000000000000000)⟩
theorem valid4001 : certificate4001.Valid := by decide +kernel
theorem sound4001 : certificate4001.Sound := rat_cut_bin_certificate_sound certificate4001 profilesValid4001 numericValid4001 valid4001

def retention4002 : RatCutRetentionCertificate := ⟨(21/500),(43/1000),(16000000000000000000/134129227617246420223),(462100736793514429/250000000000000000),(39/20),(342830500905530713304458695488970749279/184840294717405771600000000000000000000),false,MergedCutProfiles.Batch605.profile24211,(fun _ => MergedCutProfiles.Batch605.profile24211)⟩
theorem profilesValid4002 : retention4002.ProfilesValid := by
  exact MergedCutProfiles.Batch605.valid24211
theorem numericValid4002 : retention4002.NumericValid := by decide +kernel
def certificate4002 : RatCutBinCertificate := ⟨⟨retention4002,(945455743074570371/500000000000000000),(21376650541548341/250000000000000000),(2341859175842730431/200000000000000000),(3158318854834120979897/500000000000000000),(913906354739370949/500000000000000000)⟩,(999724943860244807/1000000000000000000),(464859246882683897/1000000000000000000),(179048816746500351/1000000000000000000),(66575280497330649/500000000000000000)⟩
theorem valid4002 : certificate4002.Valid := by decide +kernel
theorem sound4002 : certificate4002.Sound := rat_cut_bin_certificate_sound certificate4002 profilesValid4002 numericValid4002 valid4002

def retention4003 : RatCutRetentionCertificate := ⟨(21/500),(43/1000),(1/2),64,1,(63846487671256044251940764516727514191/64000000000000000000000000000000000000),false,MergedCutProfiles.Batch359.profile14365,(fun _ => MergedCutProfiles.Batch359.profile14365)⟩
theorem profilesValid4003 : retention4003.ProfilesValid := by
  exact MergedCutProfiles.Batch359.valid14365
theorem numericValid4003 : retention4003.NumericValid := by decide +kernel
def certificate4003 : RatCutBinCertificate := ⟨⟨retention4003,(945455743074570371/500000000000000000),(21376650541548341/250000000000000000),(2341859175842730431/200000000000000000),(3158318854834120979897/500000000000000000),(983793071563990579/1000000000000000000)⟩,(999724943860244807/1000000000000000000),(108625693768830797/200000000000000000),(125340800231365061/1000000000000000000),(60704449245498259/500000000000000000)⟩
theorem valid4003 : certificate4003.Valid := by decide +kernel
theorem sound4003 : certificate4003.Sound := rat_cut_bin_certificate_sound certificate4003 profilesValid4003 numericValid4003 valid4003

def retention4004 : RatCutRetentionCertificate := ⟨(21/500),(43/1000),(16000000000000000000/134129227617246420223),(12131603791899468429/500000000000000000),1,(1380422973127701214821867076046179549/758225236993716776812500000000000000),false,MergedCutProfiles.Batch605.profile24211,(fun _ => MergedCutProfiles.Batch605.profile24211)⟩
theorem profilesValid4004 : retention4004.ProfilesValid := by
  exact MergedCutProfiles.Batch605.valid24211
theorem numericValid4004 : retention4004.NumericValid := by decide +kernel
def certificate4004 : RatCutBinCertificate := ⟨⟨retention4004,(919265793074570371/500000000000000000),(21376650541548341/250000000000000000),(2341859175842730431/200000000000000000),(3158318854834120979897/500000000000000000),(1807171701903184843/1000000000000000000)⟩,(999732563335654247/1000000000000000000),(125969805437037/3906250000000000),(33509773235684093/40000000000000000),(1408616444297597797/1000000000000000000)⟩
theorem valid4004 : certificate4004.Valid := by decide +kernel
theorem sound4004 : certificate4004.Sound := rat_cut_bin_certificate_sound certificate4004 profilesValid4004 numericValid4004 valid4004

def retention4005 : RatCutRetentionCertificate := ⟨(21/500),(43/1000),(1/2),64,1,(63846487671256044251940764516727514191/64000000000000000000000000000000000000),false,MergedCutProfiles.Batch359.profile14365,(fun _ => MergedCutProfiles.Batch359.profile14365)⟩
theorem profilesValid4005 : retention4005.ProfilesValid := by
  exact MergedCutProfiles.Batch359.valid14365
theorem numericValid4005 : retention4005.NumericValid := by decide +kernel
def certificate4005 : RatCutBinCertificate := ⟨⟨retention4005,(919265793074570371/500000000000000000),(21376650541548341/250000000000000000),(2341859175842730431/200000000000000000),(3158318854834120979897/500000000000000000),(984175573489326557/1000000000000000000)⟩,(999732563335654247/1000000000000000000),(14803802008485891/250000000000000000),(764095608552327487/1000000000000000000),(370207608238175417/500000000000000000)⟩
theorem valid4005 : certificate4005.Valid := by decide +kernel
theorem sound4005 : certificate4005.Sound := rat_cut_bin_certificate_sound certificate4005 profilesValid4005 numericValid4005 valid4005

def retention4006 : RatCutRetentionCertificate := ⟨(43/1000),(11/250),(606577015808973708/509598721095730805365),(600571302781162087/1000000000000000000),4,(9067532972540577417/4000000000000000000),true,MergedCutProfiles.Batch605.profile24212,![MergedCutProfiles.Batch605.profile24212,MergedCutProfiles.Batch605.profile24213,MergedCutProfiles.Batch605.profile24214,MergedCutProfiles.Batch605.profile24215,MergedCutProfiles.Batch605.profile24216,MergedCutProfiles.Batch605.profile24217,MergedCutProfiles.Batch605.profile24218,MergedCutProfiles.Batch605.profile24219,MergedCutProfiles.Batch605.profile24220,MergedCutProfiles.Batch478.profile19133,MergedCutProfiles.Batch605.profile24221,MergedCutProfiles.Batch605.profile24222,MergedCutProfiles.Batch478.profile19145,MergedCutProfiles.Batch605.profile24223,MergedCutProfiles.Batch605.profile24224,MergedCutProfiles.Batch605.profile24225]⟩
theorem profilesValid4006 : retention4006.ProfilesValid := by
  change ∀ j : Fin 16, (retention4006.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch605.valid24212
  · exact MergedCutProfiles.Batch605.valid24213
  · exact MergedCutProfiles.Batch605.valid24214
  · exact MergedCutProfiles.Batch605.valid24215
  · exact MergedCutProfiles.Batch605.valid24216
  · exact MergedCutProfiles.Batch605.valid24217
  · exact MergedCutProfiles.Batch605.valid24218
  · exact MergedCutProfiles.Batch605.valid24219
  · exact MergedCutProfiles.Batch605.valid24220
  · exact MergedCutProfiles.Batch478.valid19133
  · exact MergedCutProfiles.Batch605.valid24221
  · exact MergedCutProfiles.Batch605.valid24222
  · exact MergedCutProfiles.Batch478.valid19145
  · exact MergedCutProfiles.Batch605.valid24223
  · exact MergedCutProfiles.Batch605.valid24224
  · exact MergedCutProfiles.Batch605.valid24225
theorem numericValid4006 : retention4006.NumericValid := by decide +kernel
def certificate4006 : RatCutBinCertificate := ⟨⟨retention4006,(189524127631560059/100000000000000000),(5622540848385301/62500000000000000),(11894089317798289217/1000000000000000000),(243784539652001747163/40000000000000000),(2209544446712502107/1000000000000000000)⟩,(999715612519901377/1000000000000000000),(686720399967258713/1000000000000000000),(55190806706963633/1000000000000000000),(24778503015112327/1000000000000000000)⟩
theorem valid4006 : certificate4006.Valid := by decide +kernel
theorem sound4006 : certificate4006.Sound := rat_cut_bin_certificate_sound certificate4006 profilesValid4006 numericValid4006 valid4006

def retention4007 : RatCutRetentionCertificate := ⟨(43/1000),(11/250),(222016919200000000/101919744219146161073),(151644253952243427/250000000000000000),4,(145253231924319423303/64000000000000000000),true,MergedCutProfiles.Batch605.profile24226,![MergedCutProfiles.Batch605.profile24226,MergedCutProfiles.Batch605.profile24227,MergedCutProfiles.Batch605.profile24228,MergedCutProfiles.Batch478.profile19155,MergedCutProfiles.Batch479.profile19170,MergedCutProfiles.Batch605.profile24221,MergedCutProfiles.Batch478.profile19145,MergedCutProfiles.Batch478.profile19134,MergedCutProfiles.Batch605.profile24229,MergedCutProfiles.Batch605.profile24230,MergedCutProfiles.Batch605.profile24231,MergedCutProfiles.Batch478.profile19156,MergedCutProfiles.Batch605.profile24232,MergedCutProfiles.Batch478.profile19146,MergedCutProfiles.Batch605.profile24233,MergedCutProfiles.Batch478.profile19136]⟩
theorem profilesValid4007 : retention4007.ProfilesValid := by
  change ∀ j : Fin 16, (retention4007.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch605.valid24226
  · exact MergedCutProfiles.Batch605.valid24227
  · exact MergedCutProfiles.Batch605.valid24228
  · exact MergedCutProfiles.Batch478.valid19155
  · exact MergedCutProfiles.Batch479.valid19170
  · exact MergedCutProfiles.Batch605.valid24221
  · exact MergedCutProfiles.Batch478.valid19145
  · exact MergedCutProfiles.Batch478.valid19134
  · exact MergedCutProfiles.Batch605.valid24229
  · exact MergedCutProfiles.Batch605.valid24230
  · exact MergedCutProfiles.Batch605.valid24231
  · exact MergedCutProfiles.Batch478.valid19156
  · exact MergedCutProfiles.Batch605.valid24232
  · exact MergedCutProfiles.Batch478.valid19146
  · exact MergedCutProfiles.Batch605.valid24233
  · exact MergedCutProfiles.Batch478.valid19136
theorem numericValid4007 : retention4007.NumericValid := by decide +kernel
def certificate4007 : RatCutBinCertificate := ⟨⟨retention4007,(189524127631560059/100000000000000000),(5622540848385301/62500000000000000),(11894089317798289217/1000000000000000000),(243784539652001747163/40000000000000000),(2212242955883089047/1000000000000000000)⟩,(999715612519901377/1000000000000000000),(340719970770739393/500000000000000000),(28597852554720513/500000000000000000),(12875921711374249/500000000000000000)⟩
theorem valid4007 : certificate4007.Valid := by decide +kernel
theorem sound4007 : certificate4007.Sound := rat_cut_bin_certificate_sound certificate4007 profilesValid4007 numericValid4007 valid4007

def certificates : List RatCutBinCertificate := [certificate3996,certificate3997,certificate3998,certificate3999,certificate4000,certificate4001,certificate4002,certificate4003,certificate4004,certificate4005,certificate4006,certificate4007]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound3996,List.forall_mem_cons.mpr ⟨sound3997,List.forall_mem_cons.mpr ⟨sound3998,List.forall_mem_cons.mpr ⟨sound3999,List.forall_mem_cons.mpr ⟨sound4000,List.forall_mem_cons.mpr ⟨sound4001,List.forall_mem_cons.mpr ⟨sound4002,List.forall_mem_cons.mpr ⟨sound4003,List.forall_mem_cons.mpr ⟨sound4004,List.forall_mem_cons.mpr ⟨sound4005,List.forall_mem_cons.mpr ⟨sound4006,List.forall_mem_cons.mpr ⟨sound4007,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch333
