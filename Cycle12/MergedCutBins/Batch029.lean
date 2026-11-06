import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch057
import Cycle12.MergedCutProfiles.Batch058
import Cycle12.MergedCutProfiles.Batch059

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch029

def retention348 : RatCutRetentionCertificate := ⟨(67/2000),(17/500),(11089778083941448192/22507681237218344607),(19104349057132466741/1000000000000000000),1,(15323095905336645847260375340951685559/15283479245705973392800000000000000000),false,MergedCutProfiles.Batch057.profile2305,(fun _ => MergedCutProfiles.Batch057.profile2305)⟩
theorem profilesValid348 : retention348.ProfilesValid := by
  exact MergedCutProfiles.Batch057.valid2305
theorem numericValid348 : retention348.NumericValid := by decide +kernel
def certificate348 : RatCutBinCertificate := ⟨⟨retention348,(2407250113404119921/1000000000000000000),(51337219122942991/1000000000000000000),(10301443731215175959/1000000000000000000),(29057803057295121243/62500000000000000),(990595528831844843/1000000000000000000)⟩,(497539252454225241/500000000000000000),(81318382765909617/200000000000000000),(113748259305987381/500000000000000000),(213169367345942219/1000000000000000000)⟩
theorem valid348 : certificate348.Valid := by decide +kernel
theorem sound348 : certificate348.Sound := rat_cut_bin_certificate_sound certificate348 profilesValid348 numericValid348 valid348

def retention349 : RatCutRetentionCertificate := ⟨(67/2000),(17/500),(11200675864780862674/22507681237218344607),(21659722820198141/976562500000000),1,(22064482939957974941028836628212163087/22179556167882896384000000000000000000),false,MergedCutProfiles.Batch057.profile2306,(fun _ => MergedCutProfiles.Batch057.profile2306)⟩
theorem profilesValid349 : retention349.ProfilesValid := by
  exact MergedCutProfiles.Batch057.valid2306
theorem numericValid349 : retention349.NumericValid := by decide +kernel
def certificate349 : RatCutBinCertificate := ⟨⟨retention349,(2407250113404119921/1000000000000000000),(51337219122942991/1000000000000000000),(10301443731215175959/1000000000000000000),(29057803057295121243/62500000000000000),(982815158777429509/1000000000000000000)⟩,(497539252454225241/500000000000000000),(102452665768748291/250000000000000000),(112306315393628269/500000000000000000),(105162428089993909/500000000000000000)⟩
theorem valid349 : certificate349.Valid := by decide +kernel
theorem sound349 : certificate349.Sound := rat_cut_bin_certificate_sound certificate349 profilesValid349 numericValid349 valid349

def retention350 : RatCutRetentionCertificate := ⟨(67/2000),(17/500),(1/2),(5600337932390431337/250000000000000000),1,(88736093543933596426441167801309650127/89605406918246901392000000000000000000),false,MergedCutProfiles.Batch057.profile2303,(fun _ => MergedCutProfiles.Batch057.profile2303)⟩
theorem profilesValid350 : retention350.ProfilesValid := by
  exact MergedCutProfiles.Batch057.valid2303
theorem numericValid350 : retention350.NumericValid := by decide +kernel
def certificate350 : RatCutBinCertificate := ⟨⟨retention350,(2407250113404119921/1000000000000000000),(51337219122942991/1000000000000000000),(10301443731215175959/1000000000000000000),(29057803057295121243/62500000000000000),(978301843181651631/1000000000000000000)⟩,(497539252454225241/500000000000000000),(102925322768697591/250000000000000000),(55732621970023821/250000000000000000),(51979685108613923/250000000000000000)⟩
theorem valid350 : certificate350.Valid := by decide +kernel
theorem sound350 : certificate350.Sound := rat_cut_bin_certificate_sound certificate350 profilesValid350 numericValid350 valid350

def retention351 : RatCutRetentionCertificate := ⟨(17/500),(69/2000),(755927619088420547/43606686001752681738),(748443187216257967/1000000000000000000),(69/20),(88064285329332475959/40000000000000000000),true,MergedCutProfiles.Batch057.profile2307,![MergedCutProfiles.Batch057.profile2307,MergedCutProfiles.Batch057.profile2308,MergedCutProfiles.Batch057.profile2309,MergedCutProfiles.Batch057.profile2310,MergedCutProfiles.Batch057.profile2311,MergedCutProfiles.Batch057.profile2312,MergedCutProfiles.Batch057.profile2313,MergedCutProfiles.Batch057.profile2314,MergedCutProfiles.Batch057.profile2315,MergedCutProfiles.Batch057.profile2316,MergedCutProfiles.Batch057.profile2317,MergedCutProfiles.Batch057.profile2318,MergedCutProfiles.Batch057.profile2319,MergedCutProfiles.Batch058.profile2320,MergedCutProfiles.Batch058.profile2321,MergedCutProfiles.Batch058.profile2322]⟩
theorem profilesValid351 : retention351.ProfilesValid := by
  change ∀ j : Fin 16, (retention351.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch057.valid2307
  · exact MergedCutProfiles.Batch057.valid2308
  · exact MergedCutProfiles.Batch057.valid2309
  · exact MergedCutProfiles.Batch057.valid2310
  · exact MergedCutProfiles.Batch057.valid2311
  · exact MergedCutProfiles.Batch057.valid2312
  · exact MergedCutProfiles.Batch057.valid2313
  · exact MergedCutProfiles.Batch057.valid2314
  · exact MergedCutProfiles.Batch057.valid2315
  · exact MergedCutProfiles.Batch057.valid2316
  · exact MergedCutProfiles.Batch057.valid2317
  · exact MergedCutProfiles.Batch057.valid2318
  · exact MergedCutProfiles.Batch057.valid2319
  · exact MergedCutProfiles.Batch058.valid2320
  · exact MergedCutProfiles.Batch058.valid2321
  · exact MergedCutProfiles.Batch058.valid2322
theorem numericValid351 : retention351.NumericValid := by decide +kernel
def certificate351 : RatCutBinCertificate := ⟨⟨retention351,(506210773796147677/250000000000000000),(52971016048098673/1000000000000000000),(1297103735744061133/125000000000000000),(453675255619732797693/1000000000000000000),(541486323982087899/250000000000000000)⟩,(39830597881719759/40000000000000000),(427328701726558039/1000000000000000000),(209355102666199073/1000000000000000000),(52602299192881377/500000000000000000)⟩
theorem valid351 : certificate351.Valid := by decide +kernel
theorem sound351 : certificate351.Sound := rat_cut_bin_certificate_sound certificate351 profilesValid351 numericValid351 valid351

def retention352 : RatCutRetentionCertificate := ⟨(17/500),(69/2000),(41377109772202441/2076508857226318178),(755927619088420547/1000000000000000000),(69/20),(2807432001737604052011/1280000000000000000000),true,MergedCutProfiles.Batch058.profile2323,![MergedCutProfiles.Batch058.profile2323,MergedCutProfiles.Batch058.profile2324,MergedCutProfiles.Batch058.profile2325,MergedCutProfiles.Batch058.profile2326,MergedCutProfiles.Batch058.profile2327,MergedCutProfiles.Batch058.profile2328,MergedCutProfiles.Batch058.profile2329,MergedCutProfiles.Batch058.profile2330,MergedCutProfiles.Batch058.profile2331,MergedCutProfiles.Batch058.profile2332,MergedCutProfiles.Batch058.profile2333,MergedCutProfiles.Batch058.profile2334,MergedCutProfiles.Batch058.profile2335,MergedCutProfiles.Batch058.profile2336,MergedCutProfiles.Batch058.profile2337,MergedCutProfiles.Batch058.profile2338]⟩
theorem profilesValid352 : retention352.ProfilesValid := by
  change ∀ j : Fin 16, (retention352.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch058.valid2323
  · exact MergedCutProfiles.Batch058.valid2324
  · exact MergedCutProfiles.Batch058.valid2325
  · exact MergedCutProfiles.Batch058.valid2326
  · exact MergedCutProfiles.Batch058.valid2327
  · exact MergedCutProfiles.Batch058.valid2328
  · exact MergedCutProfiles.Batch058.valid2329
  · exact MergedCutProfiles.Batch058.valid2330
  · exact MergedCutProfiles.Batch058.valid2331
  · exact MergedCutProfiles.Batch058.valid2332
  · exact MergedCutProfiles.Batch058.valid2333
  · exact MergedCutProfiles.Batch058.valid2334
  · exact MergedCutProfiles.Batch058.valid2335
  · exact MergedCutProfiles.Batch058.valid2336
  · exact MergedCutProfiles.Batch058.valid2337
  · exact MergedCutProfiles.Batch058.valid2338
theorem numericValid352 : retention352.NumericValid := by decide +kernel
def certificate352 : RatCutBinCertificate := ⟨⟨retention352,(506210773796147677/250000000000000000),(52971016048098673/1000000000000000000),(1297103735744061133/125000000000000000),(453675255619732797693/1000000000000000000),(2157644430017875777/1000000000000000000)⟩,(39830597881719759/40000000000000000),(426861120407299049/1000000000000000000),(209752888458075049/1000000000000000000),(105283099571417731/1000000000000000000)⟩
theorem valid352 : certificate352.Valid := by decide +kernel
theorem sound352 : certificate352.Sound := rat_cut_bin_certificate_sound certificate352 profilesValid352 numericValid352 valid352

def retention353 : RatCutRetentionCertificate := ⟨(17/500),(69/2000),(490393260500000000/21803343000876340869),(868919305216251261/1000000000000000000),(61/20),(2780720114343777144037/1280000000000000000000),true,MergedCutProfiles.Batch058.profile2339,![MergedCutProfiles.Batch058.profile2339,MergedCutProfiles.Batch058.profile2340,MergedCutProfiles.Batch058.profile2341,MergedCutProfiles.Batch058.profile2342,MergedCutProfiles.Batch058.profile2343,MergedCutProfiles.Batch058.profile2344,MergedCutProfiles.Batch058.profile2345,MergedCutProfiles.Batch058.profile2346,MergedCutProfiles.Batch058.profile2347,MergedCutProfiles.Batch058.profile2348,MergedCutProfiles.Batch058.profile2349,MergedCutProfiles.Batch058.profile2350,MergedCutProfiles.Batch058.profile2351,MergedCutProfiles.Batch058.profile2352,MergedCutProfiles.Batch058.profile2353,MergedCutProfiles.Batch058.profile2354]⟩
theorem profilesValid353 : retention353.ProfilesValid := by
  change ∀ j : Fin 16, (retention353.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch058.valid2339
  · exact MergedCutProfiles.Batch058.valid2340
  · exact MergedCutProfiles.Batch058.valid2341
  · exact MergedCutProfiles.Batch058.valid2342
  · exact MergedCutProfiles.Batch058.valid2343
  · exact MergedCutProfiles.Batch058.valid2344
  · exact MergedCutProfiles.Batch058.valid2345
  · exact MergedCutProfiles.Batch058.valid2346
  · exact MergedCutProfiles.Batch058.valid2347
  · exact MergedCutProfiles.Batch058.valid2348
  · exact MergedCutProfiles.Batch058.valid2349
  · exact MergedCutProfiles.Batch058.valid2350
  · exact MergedCutProfiles.Batch058.valid2351
  · exact MergedCutProfiles.Batch058.valid2352
  · exact MergedCutProfiles.Batch058.valid2353
  · exact MergedCutProfiles.Batch058.valid2354
theorem numericValid353 : retention353.NumericValid := by decide +kernel
def certificate353 : RatCutBinCertificate := ⟨⟨retention353,(506210773796147677/250000000000000000),(52971016048098673/1000000000000000000),(1297103735744061133/125000000000000000),(453675255619732797693/1000000000000000000),(1070455247209011301/500000000000000000)⟩,(39830597881719759/40000000000000000),(100631099185613111/250000000000000000),(231177329894032229/1000000000000000000),(7978768560628193/62500000000000000)⟩
theorem valid353 : certificate353.Valid := by decide +kernel
theorem sound353 : certificate353.Sound := rat_cut_bin_certificate_sound certificate353 profilesValid353 numericValid353 valid353

def retention354 : RatCutRetentionCertificate := ⟨(17/500),(69/2000),(1060246681743377215/43606686001752681738),(980786521/1000000000),(11/4),(34506955254132149737/16000000000000000000),true,MergedCutProfiles.Batch058.profile2355,![MergedCutProfiles.Batch058.profile2355,MergedCutProfiles.Batch058.profile2356,MergedCutProfiles.Batch058.profile2357,MergedCutProfiles.Batch058.profile2358,MergedCutProfiles.Batch057.profile2313,MergedCutProfiles.Batch058.profile2359,MergedCutProfiles.Batch059.profile2360,MergedCutProfiles.Batch059.profile2361,MergedCutProfiles.Batch058.profile2333,MergedCutProfiles.Batch058.profile2320,MergedCutProfiles.Batch059.profile2362,MergedCutProfiles.Batch058.profile2351,MergedCutProfiles.Batch058.profile2352,MergedCutProfiles.Batch059.profile2363,MergedCutProfiles.Batch059.profile2364,MergedCutProfiles.Batch059.profile2365]⟩
theorem profilesValid354 : retention354.ProfilesValid := by
  change ∀ j : Fin 16, (retention354.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch058.valid2355
  · exact MergedCutProfiles.Batch058.valid2356
  · exact MergedCutProfiles.Batch058.valid2357
  · exact MergedCutProfiles.Batch058.valid2358
  · exact MergedCutProfiles.Batch057.valid2313
  · exact MergedCutProfiles.Batch058.valid2359
  · exact MergedCutProfiles.Batch059.valid2360
  · exact MergedCutProfiles.Batch059.valid2361
  · exact MergedCutProfiles.Batch058.valid2333
  · exact MergedCutProfiles.Batch058.valid2320
  · exact MergedCutProfiles.Batch059.valid2362
  · exact MergedCutProfiles.Batch058.valid2351
  · exact MergedCutProfiles.Batch058.valid2352
  · exact MergedCutProfiles.Batch059.valid2363
  · exact MergedCutProfiles.Batch059.valid2364
  · exact MergedCutProfiles.Batch059.valid2365
theorem numericValid354 : retention354.NumericValid := by decide +kernel
def certificate354 : RatCutBinCertificate := ⟨⟨retention354,(506210773796147677/250000000000000000),(52971016048098673/1000000000000000000),(1297103735744061133/125000000000000000),(453675255619732797693/1000000000000000000),(1064129328001367253/500000000000000000)⟩,(39830597881719759/40000000000000000),(383675283535703809/1000000000000000000),(49755489792354141/200000000000000000),(29774278492443171/200000000000000000)⟩
theorem valid354 : certificate354.Valid := by decide +kernel
theorem sound354 : certificate354.Sound := rat_cut_bin_certificate_sound certificate354 profilesValid354 numericValid354 valid354

def retention355 : RatCutRetentionCertificate := ⟨(17/500),(69/2000),(709221400795122699/14535562000584227246),(212049336348675443/200000000000000000),(51/20),(26315107838925900669/12800000000000000000),true,MergedCutProfiles.Batch059.profile2366,![MergedCutProfiles.Batch059.profile2366,MergedCutProfiles.Batch058.profile2358,MergedCutProfiles.Batch058.profile2359,MergedCutProfiles.Batch059.profile2367,MergedCutProfiles.Batch058.profile2320,MergedCutProfiles.Batch059.profile2368,MergedCutProfiles.Batch059.profile2369,MergedCutProfiles.Batch059.profile2365,MergedCutProfiles.Batch059.profile2370,MergedCutProfiles.Batch059.profile2371,MergedCutProfiles.Batch059.profile2372,MergedCutProfiles.Batch059.profile2373,MergedCutProfiles.Batch059.profile2374,MergedCutProfiles.Batch059.profile2375,MergedCutProfiles.Batch059.profile2376,MergedCutProfiles.Batch059.profile2377]⟩
theorem profilesValid355 : retention355.ProfilesValid := by
  change ∀ j : Fin 16, (retention355.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch059.valid2366
  · exact MergedCutProfiles.Batch058.valid2358
  · exact MergedCutProfiles.Batch058.valid2359
  · exact MergedCutProfiles.Batch059.valid2367
  · exact MergedCutProfiles.Batch058.valid2320
  · exact MergedCutProfiles.Batch059.valid2368
  · exact MergedCutProfiles.Batch059.valid2369
  · exact MergedCutProfiles.Batch059.valid2365
  · exact MergedCutProfiles.Batch059.valid2370
  · exact MergedCutProfiles.Batch059.valid2371
  · exact MergedCutProfiles.Batch059.valid2372
  · exact MergedCutProfiles.Batch059.valid2373
  · exact MergedCutProfiles.Batch059.valid2374
  · exact MergedCutProfiles.Batch059.valid2375
  · exact MergedCutProfiles.Batch059.valid2376
  · exact MergedCutProfiles.Batch059.valid2377
theorem numericValid355 : retention355.NumericValid := by decide +kernel
def certificate355 : RatCutBinCertificate := ⟨⟨retention355,(506210773796147677/250000000000000000),(52971016048098673/1000000000000000000),(1297103735744061133/125000000000000000),(453675255619732797693/1000000000000000000),(507377276041214583/250000000000000000)⟩,(39830597881719759/40000000000000000),(48672058861859071/125000000000000000),(7604951202515507/31250000000000000),(37225815470934017/250000000000000000)⟩
theorem valid355 : certificate355.Valid := by decide +kernel
theorem sound355 : certificate355.Sound := rat_cut_bin_certificate_sound certificate355 profilesValid355 numericValid355 valid355

def retention356 : RatCutRetentionCertificate := ⟨(17/500),(69/2000),(1944046967650582706/7267781000292113623),(2127664202385368097/1000000000000000000),(8/5),(315183534408047342877302245669889504279/212766420238536809700000000000000000000),false,MergedCutProfiles.Batch059.profile2378,(fun _ => MergedCutProfiles.Batch059.profile2378)⟩
theorem profilesValid356 : retention356.ProfilesValid := by
  exact MergedCutProfiles.Batch059.valid2378
theorem numericValid356 : retention356.NumericValid := by decide +kernel
def certificate356 : RatCutBinCertificate := ⟨⟨retention356,(506210773796147677/250000000000000000),(52971016048098673/1000000000000000000),(1297103735744061133/125000000000000000),(453675255619732797693/1000000000000000000),(732410373542278509/500000000000000000)⟩,(39830597881719759/40000000000000000),(10705709007830303/25000000000000000),(20859117388145567/100000000000000000),(18722115762055231/125000000000000000)⟩
theorem valid356 : certificate356.Valid := by decide +kernel
theorem sound356 : certificate356.Sound := rat_cut_bin_certificate_sound certificate356 profilesValid356 numericValid356 valid356

def retention357 : RatCutRetentionCertificate := ⟨(17/500),(69/2000),(10386463213364408572/21803343000876340869),(2916070451475874059/250000000000000000),(21/20),(1218095787326438417923477639104980536679/1166428180590349623600000000000000000000),false,MergedCutProfiles.Batch059.profile2379,(fun _ => MergedCutProfiles.Batch059.profile2379)⟩
theorem profilesValid357 : retention357.ProfilesValid := by
  exact MergedCutProfiles.Batch059.valid2379
theorem numericValid357 : retention357.NumericValid := by decide +kernel
def certificate357 : RatCutBinCertificate := ⟨⟨retention357,(506210773796147677/250000000000000000),(52971016048098673/1000000000000000000),(1297103735744061133/125000000000000000),(453675255619732797693/1000000000000000000),(516721179723875849/500000000000000000)⟩,(39830597881719759/40000000000000000),(478917691839665919/1000000000000000000),(84245145988707913/500000000000000000),(3820524463302341/25000000000000000)⟩
theorem valid357 : certificate357.Valid := by decide +kernel
theorem sound357 : certificate357.Sound := rat_cut_bin_certificate_sound certificate357 profilesValid357 numericValid357 valid357

def retention358 : RatCutRetentionCertificate := ⟨(17/500),(69/2000),(7205463513029659435/14535562000584227246),(2596615803341102143/125000000000000000),1,(663274880112178211799869948235645483/664733645655322148608000000000000000),false,MergedCutProfiles.Batch059.profile2380,(fun _ => MergedCutProfiles.Batch059.profile2380)⟩
theorem profilesValid358 : retention358.ProfilesValid := by
  exact MergedCutProfiles.Batch059.valid2380
theorem numericValid358 : retention358.NumericValid := by decide +kernel
def certificate358 : RatCutBinCertificate := ⟨⟨retention358,(506210773796147677/250000000000000000),(52971016048098673/1000000000000000000),(1297103735744061133/125000000000000000),(453675255619732797693/1000000000000000000),(493734566743589367/500000000000000000)⟩,(39830597881719759/40000000000000000),(488103192493630001/1000000000000000000),(1618152413180933/10000000000000000),(151874261479889277/1000000000000000000)⟩
theorem valid358 : certificate358.Valid := by decide +kernel
theorem sound358 : certificate358.Sound := rat_cut_bin_certificate_sound certificate358 profilesValid358 numericValid358 valid358

def retention359 : RatCutRetentionCertificate := ⟨(17/500),(69/2000),(1/2),(4323278107817795661/200000000000000000),1,(2674740151651703341600564670788194907/2702048817386122288125000000000000000),false,MergedCutProfiles.Batch059.profile2381,(fun _ => MergedCutProfiles.Batch059.profile2381)⟩
theorem profilesValid359 : retention359.ProfilesValid := by
  exact MergedCutProfiles.Batch059.valid2381
theorem numericValid359 : retention359.NumericValid := by decide +kernel
def certificate359 : RatCutBinCertificate := ⟨⟨retention359,(506210773796147677/250000000000000000),(52971016048098673/1000000000000000000),(1297103735744061133/125000000000000000),(453675255619732797693/1000000000000000000),(244889248905831193/250000000000000000)⟩,(39830597881719759/40000000000000000),(245692649710588969/500000000000000000),(79736119697304331/500000000000000000),(148791962102037667/1000000000000000000)⟩
theorem valid359 : certificate359.Valid := by decide +kernel
theorem sound359 : certificate359.Sound := rat_cut_bin_certificate_sound certificate359 profilesValid359 numericValid359 valid359

def certificates : List RatCutBinCertificate := [certificate348,certificate349,certificate350,certificate351,certificate352,certificate353,certificate354,certificate355,certificate356,certificate357,certificate358,certificate359]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound348,List.forall_mem_cons.mpr ⟨sound349,List.forall_mem_cons.mpr ⟨sound350,List.forall_mem_cons.mpr ⟨sound351,List.forall_mem_cons.mpr ⟨sound352,List.forall_mem_cons.mpr ⟨sound353,List.forall_mem_cons.mpr ⟨sound354,List.forall_mem_cons.mpr ⟨sound355,List.forall_mem_cons.mpr ⟨sound356,List.forall_mem_cons.mpr ⟨sound357,List.forall_mem_cons.mpr ⟨sound358,List.forall_mem_cons.mpr ⟨sound359,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch029
