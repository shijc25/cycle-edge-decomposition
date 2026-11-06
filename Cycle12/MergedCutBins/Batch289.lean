import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch532
import Cycle12.MergedCutProfiles.Batch533
import Cycle12.MergedCutProfiles.Batch534

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch289

def retention3468 : RatCutRetentionCertificate := ⟨(31/500),(249/4000),(1076907039219298451/57204096836931725928),(181863211973439319/200000000000000000),(29/10),(35406771178918804801/16000000000000000000),true,MergedCutProfiles.Batch532.profile21299,![MergedCutProfiles.Batch532.profile21299,MergedCutProfiles.Batch532.profile21300,MergedCutProfiles.Batch532.profile21301,MergedCutProfiles.Batch532.profile21302,MergedCutProfiles.Batch532.profile21303,MergedCutProfiles.Batch532.profile21304,MergedCutProfiles.Batch532.profile21305,MergedCutProfiles.Batch532.profile21306,MergedCutProfiles.Batch532.profile21307,MergedCutProfiles.Batch532.profile21308,MergedCutProfiles.Batch532.profile21295,MergedCutProfiles.Batch532.profile21309,MergedCutProfiles.Batch532.profile21310,MergedCutProfiles.Batch532.profile21311,MergedCutProfiles.Batch532.profile21312,MergedCutProfiles.Batch532.profile21313]⟩
theorem profilesValid3468 : retention3468.ProfilesValid := by
  change ∀ j : Fin 16, (retention3468.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch532.valid21299
  · exact MergedCutProfiles.Batch532.valid21300
  · exact MergedCutProfiles.Batch532.valid21301
  · exact MergedCutProfiles.Batch532.valid21302
  · exact MergedCutProfiles.Batch532.valid21303
  · exact MergedCutProfiles.Batch532.valid21304
  · exact MergedCutProfiles.Batch532.valid21305
  · exact MergedCutProfiles.Batch532.valid21306
  · exact MergedCutProfiles.Batch532.valid21307
  · exact MergedCutProfiles.Batch532.valid21308
  · exact MergedCutProfiles.Batch532.valid21295
  · exact MergedCutProfiles.Batch532.valid21309
  · exact MergedCutProfiles.Batch532.valid21310
  · exact MergedCutProfiles.Batch532.valid21311
  · exact MergedCutProfiles.Batch532.valid21312
  · exact MergedCutProfiles.Batch532.valid21313
theorem numericValid3468 : retention3468.NumericValid := by decide +kernel
def certificate3468 : RatCutBinCertificate := ⟨⟨retention3468,(1118732903210718603/500000000000000000),(99557273866218649/500000000000000000),(823257618475654671/50000000000000000),(11791708434151031007/12500000000000000),(2134449087876797383/1000000000000000000)⟩,(499047495099218751/500000000000000000),(63487816573830759/200000000000000000),(159147467613609899/500000000000000000),(91366653868346803/500000000000000000)⟩
theorem valid3468 : certificate3468.Valid := by decide +kernel
theorem sound3468 : certificate3468.Sound := rat_cut_bin_certificate_sound certificate3468 profilesValid3468 numericValid3468 valid3468

def retention3469 : RatCutRetentionCertificate := ⟨(31/500),(249/4000),(45689246000000000/2383504034872155247),(1076907039219298451/1000000000000000000),(5/2),(35103987316727995517/16000000000000000000),true,MergedCutProfiles.Batch532.profile21299,![MergedCutProfiles.Batch532.profile21299,MergedCutProfiles.Batch532.profile21314,MergedCutProfiles.Batch532.profile21315,MergedCutProfiles.Batch532.profile21316,MergedCutProfiles.Batch532.profile21288,MergedCutProfiles.Batch532.profile21317,MergedCutProfiles.Batch532.profile21318,MergedCutProfiles.Batch532.profile21319,MergedCutProfiles.Batch533.profile21320,MergedCutProfiles.Batch533.profile21321,MergedCutProfiles.Batch533.profile21322,MergedCutProfiles.Batch533.profile21323,MergedCutProfiles.Batch533.profile21324,MergedCutProfiles.Batch533.profile21325,MergedCutProfiles.Batch533.profile21326,MergedCutProfiles.Batch533.profile21327]⟩
theorem profilesValid3469 : retention3469.ProfilesValid := by
  change ∀ j : Fin 16, (retention3469.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch532.valid21299
  · exact MergedCutProfiles.Batch532.valid21314
  · exact MergedCutProfiles.Batch532.valid21315
  · exact MergedCutProfiles.Batch532.valid21316
  · exact MergedCutProfiles.Batch532.valid21288
  · exact MergedCutProfiles.Batch532.valid21317
  · exact MergedCutProfiles.Batch532.valid21318
  · exact MergedCutProfiles.Batch532.valid21319
  · exact MergedCutProfiles.Batch533.valid21320
  · exact MergedCutProfiles.Batch533.valid21321
  · exact MergedCutProfiles.Batch533.valid21322
  · exact MergedCutProfiles.Batch533.valid21323
  · exact MergedCutProfiles.Batch533.valid21324
  · exact MergedCutProfiles.Batch533.valid21325
  · exact MergedCutProfiles.Batch533.valid21326
  · exact MergedCutProfiles.Batch533.valid21327
theorem numericValid3469 : retention3469.NumericValid := by decide +kernel
def certificate3469 : RatCutBinCertificate := ⟨⟨retention3469,(1118732903210718603/500000000000000000),(99557273866218649/500000000000000000),(823257618475654671/50000000000000000),(11791708434151031007/12500000000000000),(1701079378312053/800000000000000)⟩,(499047495099218751/500000000000000000),(148021433988804003/500000000000000000),(85893269668014247/250000000000000000),(221564531441420587/1000000000000000000)⟩
theorem valid3469 : certificate3469.Valid := by decide +kernel
theorem sound3469 : certificate3469.Sound := rat_cut_bin_certificate_sound certificate3469 profilesValid3469 numericValid3469 valid3469

def retention3470 : RatCutRetentionCertificate := ⟨(31/500),(249/4000),(1177797368844266171/57204096836931725928),(68533869/62500000),(49/20),(8731851872989238979/4000000000000000000),true,MergedCutProfiles.Batch533.profile21328,![MergedCutProfiles.Batch533.profile21328,MergedCutProfiles.Batch533.profile21329,MergedCutProfiles.Batch533.profile21330,MergedCutProfiles.Batch533.profile21331,MergedCutProfiles.Batch533.profile21332,MergedCutProfiles.Batch533.profile21333,MergedCutProfiles.Batch533.profile21334,MergedCutProfiles.Batch533.profile21335,MergedCutProfiles.Batch533.profile21336,MergedCutProfiles.Batch532.profile21295,MergedCutProfiles.Batch532.profile21309,MergedCutProfiles.Batch533.profile21337,MergedCutProfiles.Batch533.profile21338,MergedCutProfiles.Batch533.profile21326,MergedCutProfiles.Batch533.profile21339,MergedCutProfiles.Batch533.profile21340]⟩
theorem profilesValid3470 : retention3470.ProfilesValid := by
  change ∀ j : Fin 16, (retention3470.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch533.valid21328
  · exact MergedCutProfiles.Batch533.valid21329
  · exact MergedCutProfiles.Batch533.valid21330
  · exact MergedCutProfiles.Batch533.valid21331
  · exact MergedCutProfiles.Batch533.valid21332
  · exact MergedCutProfiles.Batch533.valid21333
  · exact MergedCutProfiles.Batch533.valid21334
  · exact MergedCutProfiles.Batch533.valid21335
  · exact MergedCutProfiles.Batch533.valid21336
  · exact MergedCutProfiles.Batch532.valid21295
  · exact MergedCutProfiles.Batch532.valid21309
  · exact MergedCutProfiles.Batch533.valid21337
  · exact MergedCutProfiles.Batch533.valid21338
  · exact MergedCutProfiles.Batch533.valid21326
  · exact MergedCutProfiles.Batch533.valid21339
  · exact MergedCutProfiles.Batch533.valid21340
theorem numericValid3470 : retention3470.NumericValid := by decide +kernel
def certificate3470 : RatCutBinCertificate := ⟨⟨retention3470,(1118732903210718603/500000000000000000),(99557273866218649/500000000000000000),(823257618475654671/50000000000000000),(11791708434151031007/12500000000000000),(423333194485126171/200000000000000000)⟩,(499047495099218751/500000000000000000),(73797726999386759/250000000000000000),(17230538397484193/50000000000000000),(112384487454887339/500000000000000000)⟩
theorem valid3470 : certificate3470.Valid := by decide +kernel
theorem sound3470 : certificate3470.Sound := rat_cut_bin_certificate_sound certificate3470 profilesValid3470 numericValid3470 valid3470

def retention3471 : RatCutRetentionCertificate := ⟨(31/500),(249/4000),(1205534091777220753/28602048418465862964),(1177797368844266171/1000000000000000000),(12/5),(676931012752758006871/320000000000000000000),true,MergedCutProfiles.Batch533.profile21341,![MergedCutProfiles.Batch533.profile21341,MergedCutProfiles.Batch533.profile21342,MergedCutProfiles.Batch532.profile21290,MergedCutProfiles.Batch532.profile21307,MergedCutProfiles.Batch533.profile21322,MergedCutProfiles.Batch533.profile21343,MergedCutProfiles.Batch533.profile21344,MergedCutProfiles.Batch533.profile21345,MergedCutProfiles.Batch533.profile21346,MergedCutProfiles.Batch533.profile21347,MergedCutProfiles.Batch533.profile21348,MergedCutProfiles.Batch533.profile21349,MergedCutProfiles.Batch533.profile21350,MergedCutProfiles.Batch533.profile21351,MergedCutProfiles.Batch533.profile21352,MergedCutProfiles.Batch533.profile21353]⟩
theorem profilesValid3471 : retention3471.ProfilesValid := by
  change ∀ j : Fin 16, (retention3471.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch533.valid21341
  · exact MergedCutProfiles.Batch533.valid21342
  · exact MergedCutProfiles.Batch532.valid21290
  · exact MergedCutProfiles.Batch532.valid21307
  · exact MergedCutProfiles.Batch533.valid21322
  · exact MergedCutProfiles.Batch533.valid21343
  · exact MergedCutProfiles.Batch533.valid21344
  · exact MergedCutProfiles.Batch533.valid21345
  · exact MergedCutProfiles.Batch533.valid21346
  · exact MergedCutProfiles.Batch533.valid21347
  · exact MergedCutProfiles.Batch533.valid21348
  · exact MergedCutProfiles.Batch533.valid21349
  · exact MergedCutProfiles.Batch533.valid21350
  · exact MergedCutProfiles.Batch533.valid21351
  · exact MergedCutProfiles.Batch533.valid21352
  · exact MergedCutProfiles.Batch533.valid21353
theorem numericValid3471 : retention3471.NumericValid := by decide +kernel
def certificate3471 : RatCutBinCertificate := ⟨⟨retention3471,(1118732903210718603/500000000000000000),(99557273866218649/500000000000000000),(823257618475654671/50000000000000000),(11791708434151031007/12500000000000000),(2050465671975832869/1000000000000000000)⟩,(499047495099218751/500000000000000000),(148051769622064029/500000000000000000),(85874818510066721/250000000000000000),(112425806228901847/500000000000000000)⟩
theorem valid3471 : certificate3471.Valid := by decide +kernel
theorem sound3471 : certificate3471.Sound := rat_cut_bin_certificate_sound certificate3471 profilesValid3471 numericValid3471 valid3471

def retention3472 : RatCutRetentionCertificate := ⟨(31/500),(249/4000),(15345640354279975015/57204096836931725928),(1205534091777220753/500000000000000000),(3/2),(14303028717542641696297706239442063367/9644272734217766024000000000000000000),false,MergedCutProfiles.Batch533.profile21354,(fun _ => MergedCutProfiles.Batch533.profile21354)⟩
theorem profilesValid3472 : retention3472.ProfilesValid := by
  exact MergedCutProfiles.Batch533.valid21354
theorem numericValid3472 : retention3472.NumericValid := by decide +kernel
def certificate3472 : RatCutBinCertificate := ⟨⟨retention3472,(1118732903210718603/500000000000000000),(99557273866218649/500000000000000000),(823257618475654671/50000000000000000),(11791708434151031007/12500000000000000),(288494031726821239/200000000000000000)⟩,(499047495099218751/500000000000000000),(168175362631268833/500000000000000000),(297152713204222859/1000000000000000000),(225241149653153911/1000000000000000000)⟩
theorem valid3472 : certificate3472.Valid := by decide +kernel
theorem sound3472 : certificate3472.Sound := rat_cut_bin_certificate_sound certificate3472 profilesValid3472 numericValid3472 valid3472

def retention3473 : RatCutRetentionCertificate := ⟨(31/500),(249/4000),(9200783554116272987/19068032278977241976),(3069128070855995003/200000000000000000),1,(1955053269425069662332491449402036977/1918205044284996876875000000000000000),false,MergedCutProfiles.Batch533.profile21355,(fun _ => MergedCutProfiles.Batch533.profile21355)⟩
theorem profilesValid3473 : retention3473.ProfilesValid := by
  exact MergedCutProfiles.Batch533.valid21355
theorem numericValid3473 : retention3473.NumericValid := by decide +kernel
def certificate3473 : RatCutBinCertificate := ⟨⟨retention3473,(1118732903210718603/500000000000000000),(99557273866218649/500000000000000000),(823257618475654671/50000000000000000),(11791708434151031007/12500000000000000),(248037874501011193/250000000000000000)⟩,(499047495099218751/500000000000000000),(78010340706651823/200000000000000000),(121361087650651773/500000000000000000),(225744479484147389/1000000000000000000)⟩
theorem valid3473 : certificate3473.Valid := by decide +kernel
theorem sound3473 : certificate3473.Sound := rat_cut_bin_certificate_sound certificate3473 profilesValid3473 numericValid3473 valid3473

def retention3474 : RatCutRetentionCertificate := ⟨(31/500),(249/4000),(14219364744884325263/28602048418465862964),(27602350662348818961/1000000000000000000),1,(3443912725324304259017510349265303969/3450293832793602370125000000000000000),false,MergedCutProfiles.Batch533.profile21356,(fun _ => MergedCutProfiles.Batch533.profile21356)⟩
theorem profilesValid3474 : retention3474.ProfilesValid := by
  exact MergedCutProfiles.Batch533.valid21356
theorem numericValid3474 : retention3474.NumericValid := by decide +kernel
def certificate3474 : RatCutBinCertificate := ⟨⟨retention3474,(1118732903210718603/500000000000000000),(99557273866218649/500000000000000000),(823257618475654671/50000000000000000),(11791708434151031007/12500000000000000),(485546240910200877/500000000000000000)⟩,(499047495099218751/500000000000000000),(24383834732571589/62500000000000000),(30329723134008299/125000000000000000),(56793031430749329/250000000000000000)⟩
theorem valid3474 : certificate3474.Valid := by decide +kernel
theorem sound3474 : certificate3474.Sound := rat_cut_bin_certificate_sound certificate3474 profilesValid3474 numericValid3474 valid3474

def retention3475 : RatCutRetentionCertificate := ⟨(31/500),(249/4000),(1/2),(14219364744884325263/500000000000000000),1,(110288975403066858053749629545763837/111088787069408791117187500000000000),false,MergedCutProfiles.Batch533.profile21357,(fun _ => MergedCutProfiles.Batch533.profile21357)⟩
theorem profilesValid3475 : retention3475.ProfilesValid := by
  exact MergedCutProfiles.Batch533.valid21357
theorem numericValid3475 : retention3475.NumericValid := by decide +kernel
def certificate3475 : RatCutBinCertificate := ⟨⟨retention3475,(1118732903210718603/500000000000000000),(99557273866218649/500000000000000000),(823257618475654671/50000000000000000),(11791708434151031007/12500000000000000),(965742175213758633/1000000000000000000)⟩,(499047495099218751/500000000000000000),(391992910156328563/1000000000000000000),(240899500682012737/1000000000000000000),(224567538918822077/1000000000000000000)⟩
theorem valid3475 : certificate3475.Valid := by decide +kernel
theorem sound3475 : certificate3475.Sound := rat_cut_bin_certificate_sound certificate3475 profilesValid3475 numericValid3475 valid3475

def retention3476 : RatCutRetentionCertificate := ⟨(31/500),(249/4000),(463151814229518335/1003580646261960104),(2275889851150464741/250000000000000000),1,(2542255248937649809710338094898454793/2427615841227162390400000000000000000),false,MergedCutProfiles.Batch533.profile21358,(fun _ => MergedCutProfiles.Batch533.profile21358)⟩
theorem profilesValid3476 : retention3476.ProfilesValid := by
  exact MergedCutProfiles.Batch533.valid21358
theorem numericValid3476 : retention3476.NumericValid := by decide +kernel
def certificate3476 : RatCutBinCertificate := ⟨⟨retention3476,(1149120397710718603/500000000000000000),(99557273866218649/500000000000000000),(823257618475654671/50000000000000000),(11791708434151031007/12500000000000000),(1019429569036340621/1000000000000000000)⟩,(998043220646851813/1000000000000000000),(117418851443285823/1000000000000000000),(628864530436210857/1000000000000000000),(575322716180985151/1000000000000000000)⟩
theorem valid3476 : certificate3476.Valid := by decide +kernel
theorem sound3476 : certificate3476.Sound := rat_cut_bin_certificate_sound certificate3476 profilesValid3476 numericValid3476 valid3476

def retention3477 : RatCutRetentionCertificate := ⟨(31/500),(249/4000),(9434667235131337367/19068032278977241976),(5279930682216509019/200000000000000000),1,(26462092000579559684375766011761416941/26399653411082545095000000000000000000),false,MergedCutProfiles.Batch533.profile21359,(fun _ => MergedCutProfiles.Batch533.profile21359)⟩
theorem profilesValid3477 : retention3477.ProfilesValid := by
  exact MergedCutProfiles.Batch533.valid21359
theorem numericValid3477 : retention3477.NumericValid := by decide +kernel
def certificate3477 : RatCutBinCertificate := ⟨⟨retention3477,(1149120397710718603/500000000000000000),(99557273866218649/500000000000000000),(823257618475654671/50000000000000000),(11791708434151031007/12500000000000000),(194914415435365601/200000000000000000)⟩,(998043220646851813/1000000000000000000),(12282339287856731/100000000000000000),(617680669799780657/1000000000000000000),(18105625403806921/31250000000000000)⟩
theorem valid3477 : certificate3477.Valid := by decide +kernel
theorem sound3477 : certificate3477.Sound := rat_cut_bin_certificate_sound certificate3477 profilesValid3477 numericValid3477 valid3477

def retention3478 : RatCutRetentionCertificate := ⟨(31/500),(249/4000),(9529013907482650741/19068032278977241976),(28304001705394012101/1000000000000000000),1,(702841084606104631022530570465128443/707600042634850302525000000000000000),false,MergedCutProfiles.Batch534.profile21360,(fun _ => MergedCutProfiles.Batch534.profile21360)⟩
theorem profilesValid3478 : retention3478.ProfilesValid := by
  exact MergedCutProfiles.Batch534.valid21360
theorem numericValid3478 : retention3478.NumericValid := by decide +kernel
def certificate3478 : RatCutBinCertificate := ⟨⟨retention3478,(1149120397710718603/500000000000000000),(99557273866218649/500000000000000000),(823257618475654671/50000000000000000),(11791708434151031007/12500000000000000),(24137036788795749/25000000000000000)⟩,(998043220646851813/1000000000000000000),(15497481392777963/125000000000000000),(153828581091245417/250000000000000000),(573329402406180019/1000000000000000000)⟩
theorem valid3478 : certificate3478.Valid := by decide +kernel
theorem sound3478 : certificate3478.Sound := rat_cut_bin_certificate_sound certificate3478 profilesValid3478 numericValid3478 valid3478

def retention3479 : RatCutRetentionCertificate := ⟨(31/500),(249/4000),(1/2),(28587041722447952223/1000000000000000000),1,(73912838902749668424342846684119967/74445421152208208914062500000000000),false,MergedCutProfiles.Batch533.profile21357,(fun _ => MergedCutProfiles.Batch533.profile21357)⟩
theorem profilesValid3479 : retention3479.ProfilesValid := by
  exact MergedCutProfiles.Batch533.valid21357
theorem numericValid3479 : retention3479.NumericValid := by decide +kernel
def certificate3479 : RatCutBinCertificate := ⟨⟨retention3479,(1149120397710718603/500000000000000000),(99557273866218649/500000000000000000),(823257618475654671/50000000000000000),(11791708434151031007/12500000000000000),(241263242246154101/250000000000000000)⟩,(998043220646851813/1000000000000000000),(124034900643343931/1000000000000000000),(153800478635089747/250000000000000000),(57316599121137927/100000000000000000)⟩
theorem valid3479 : certificate3479.Valid := by decide +kernel
theorem sound3479 : certificate3479.Sound := rat_cut_bin_certificate_sound certificate3479 profilesValid3479 numericValid3479 valid3479

def certificates : List RatCutBinCertificate := [certificate3468,certificate3469,certificate3470,certificate3471,certificate3472,certificate3473,certificate3474,certificate3475,certificate3476,certificate3477,certificate3478,certificate3479]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound3468,List.forall_mem_cons.mpr ⟨sound3469,List.forall_mem_cons.mpr ⟨sound3470,List.forall_mem_cons.mpr ⟨sound3471,List.forall_mem_cons.mpr ⟨sound3472,List.forall_mem_cons.mpr ⟨sound3473,List.forall_mem_cons.mpr ⟨sound3474,List.forall_mem_cons.mpr ⟨sound3475,List.forall_mem_cons.mpr ⟨sound3476,List.forall_mem_cons.mpr ⟨sound3477,List.forall_mem_cons.mpr ⟨sound3478,List.forall_mem_cons.mpr ⟨sound3479,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch289
