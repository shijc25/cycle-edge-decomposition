import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch407
import Cycle12.MergedCutProfiles.Batch408
import Cycle12.MergedCutProfiles.Batch409
import Cycle12.MergedCutProfiles.Batch410

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch217

def retention2604 : RatCutRetentionCertificate := ⟨(61/1000),(123/2000),(97787470698466121/1962693169736233488),(495417232806112877/500000000000000000),(5/2),(3279231580529720617/1600000000000000000),true,MergedCutProfiles.Batch408.profile16328,![MergedCutProfiles.Batch408.profile16328,MergedCutProfiles.Batch408.profile16329,MergedCutProfiles.Batch408.profile16330,MergedCutProfiles.Batch408.profile16331,MergedCutProfiles.Batch408.profile16332,MergedCutProfiles.Batch408.profile16333,MergedCutProfiles.Batch408.profile16334,MergedCutProfiles.Batch408.profile16335,MergedCutProfiles.Batch408.profile16336,MergedCutProfiles.Batch408.profile16337,MergedCutProfiles.Batch408.profile16338,MergedCutProfiles.Batch408.profile16339,MergedCutProfiles.Batch408.profile16340,MergedCutProfiles.Batch408.profile16341,MergedCutProfiles.Batch408.profile16342,MergedCutProfiles.Batch408.profile16343]⟩
theorem profilesValid2604 : retention2604.ProfilesValid := by
  change ∀ j : Fin 16, (retention2604.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch408.valid16328
  · exact MergedCutProfiles.Batch408.valid16329
  · exact MergedCutProfiles.Batch408.valid16330
  · exact MergedCutProfiles.Batch408.valid16331
  · exact MergedCutProfiles.Batch408.valid16332
  · exact MergedCutProfiles.Batch408.valid16333
  · exact MergedCutProfiles.Batch408.valid16334
  · exact MergedCutProfiles.Batch408.valid16335
  · exact MergedCutProfiles.Batch408.valid16336
  · exact MergedCutProfiles.Batch408.valid16337
  · exact MergedCutProfiles.Batch408.valid16338
  · exact MergedCutProfiles.Batch408.valid16339
  · exact MergedCutProfiles.Batch408.valid16340
  · exact MergedCutProfiles.Batch408.valid16341
  · exact MergedCutProfiles.Batch408.valid16342
  · exact MergedCutProfiles.Batch408.valid16343
theorem numericValid2604 : retention2604.NumericValid := by decide +kernel
def certificate2604 : RatCutBinCertificate := ⟨⟨retention2604,(2285611066785509667/1000000000000000000),(19343761517970331/100000000000000000),(2020094325706112533/125000000000000000),(190899570021150208329/500000000000000000),(1981111177423215827/1000000000000000000)⟩,(497571832670278607/500000000000000000),(18527963174403269/62500000000000000),(85770299763364711/250000000000000000),(102390707681268293/500000000000000000)⟩
theorem valid2604 : certificate2604.Valid := by decide +kernel
theorem sound2604 : certificate2604.Sound := rat_cut_bin_certificate_sound certificate2604 profilesValid2604 numericValid2604 valid2604

def retention2605 : RatCutRetentionCertificate := ⟨(61/1000),(123/2000),(433533948696454699/3925386339472466976),(293362412095398363/250000000000000000),(9/4),(120083354604026123103/64000000000000000000),true,MergedCutProfiles.Batch408.profile16344,![MergedCutProfiles.Batch408.profile16344,MergedCutProfiles.Batch408.profile16345,MergedCutProfiles.Batch407.profile16303,MergedCutProfiles.Batch408.profile16346,MergedCutProfiles.Batch408.profile16347,MergedCutProfiles.Batch408.profile16348,MergedCutProfiles.Batch408.profile16349,MergedCutProfiles.Batch408.profile16350,MergedCutProfiles.Batch408.profile16351,MergedCutProfiles.Batch408.profile16352,MergedCutProfiles.Batch408.profile16353,MergedCutProfiles.Batch408.profile16354,MergedCutProfiles.Batch408.profile16355,MergedCutProfiles.Batch408.profile16356,MergedCutProfiles.Batch408.profile16357,MergedCutProfiles.Batch408.profile16358]⟩
theorem profilesValid2605 : retention2605.ProfilesValid := by
  change ∀ j : Fin 16, (retention2605.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch408.valid16344
  · exact MergedCutProfiles.Batch408.valid16345
  · exact MergedCutProfiles.Batch407.valid16303
  · exact MergedCutProfiles.Batch408.valid16346
  · exact MergedCutProfiles.Batch408.valid16347
  · exact MergedCutProfiles.Batch408.valid16348
  · exact MergedCutProfiles.Batch408.valid16349
  · exact MergedCutProfiles.Batch408.valid16350
  · exact MergedCutProfiles.Batch408.valid16351
  · exact MergedCutProfiles.Batch408.valid16352
  · exact MergedCutProfiles.Batch408.valid16353
  · exact MergedCutProfiles.Batch408.valid16354
  · exact MergedCutProfiles.Batch408.valid16355
  · exact MergedCutProfiles.Batch408.valid16356
  · exact MergedCutProfiles.Batch408.valid16357
  · exact MergedCutProfiles.Batch408.valid16358
theorem numericValid2605 : retention2605.NumericValid := by decide +kernel
def certificate2605 : RatCutBinCertificate := ⟨⟨retention2605,(2285611066785509667/1000000000000000000),(19343761517970331/100000000000000000),(2020094325706112533/125000000000000000),(190899570021150208329/500000000000000000),(907367744711931783/500000000000000000)⟩,(497571832670278607/500000000000000000),(30432198805198943/100000000000000000),(333615096266857143/1000000000000000000),(40985150705896481/200000000000000000)⟩
theorem valid2605 : certificate2605.Valid := by decide +kernel
theorem sound2605 : certificate2605.Sound := rat_cut_bin_certificate_sound certificate2605 profilesValid2605 numericValid2605 valid2605

def retention2606 : RatCutRetentionCertificate := ⟨(61/1000),(123/2000),(8168312543696868865/23552318036834801856),(1300601846089364097/500000000000000000),(13/10),(827653018568771605413/640000000000000000000),true,MergedCutProfiles.Batch408.profile16359,![MergedCutProfiles.Batch408.profile16359,MergedCutProfiles.Batch409.profile16360,MergedCutProfiles.Batch409.profile16361,MergedCutProfiles.Batch409.profile16362,MergedCutProfiles.Batch409.profile16363,MergedCutProfiles.Batch409.profile16364,MergedCutProfiles.Batch409.profile16365,MergedCutProfiles.Batch409.profile16366,MergedCutProfiles.Batch409.profile16367,MergedCutProfiles.Batch409.profile16368,MergedCutProfiles.Batch409.profile16369,MergedCutProfiles.Batch409.profile16370,MergedCutProfiles.Batch409.profile16371,MergedCutProfiles.Batch409.profile16372,MergedCutProfiles.Batch409.profile16373,MergedCutProfiles.Batch409.profile16374]⟩
theorem profilesValid2606 : retention2606.ProfilesValid := by
  change ∀ j : Fin 16, (retention2606.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch408.valid16359
  · exact MergedCutProfiles.Batch409.valid16360
  · exact MergedCutProfiles.Batch409.valid16361
  · exact MergedCutProfiles.Batch409.valid16362
  · exact MergedCutProfiles.Batch409.valid16363
  · exact MergedCutProfiles.Batch409.valid16364
  · exact MergedCutProfiles.Batch409.valid16365
  · exact MergedCutProfiles.Batch409.valid16366
  · exact MergedCutProfiles.Batch409.valid16367
  · exact MergedCutProfiles.Batch409.valid16368
  · exact MergedCutProfiles.Batch409.valid16369
  · exact MergedCutProfiles.Batch409.valid16370
  · exact MergedCutProfiles.Batch409.valid16371
  · exact MergedCutProfiles.Batch409.valid16372
  · exact MergedCutProfiles.Batch409.valid16373
  · exact MergedCutProfiles.Batch409.valid16374
theorem numericValid2606 : retention2606.NumericValid := by decide +kernel
def certificate2606 : RatCutBinCertificate := ⟨⟨retention2606,(2285611066785509667/1000000000000000000),(19343761517970331/100000000000000000),(2020094325706112533/125000000000000000),(190899570021150208329/500000000000000000),(1257637335777274057/1000000000000000000)⟩,(497571832670278607/500000000000000000),(356172664395532941/1000000000000000000),(34516411842663161/125000000000000000),(103276298375573399/500000000000000000)⟩
theorem valid2606 : certificate2606.Valid := by decide +kernel
theorem sound2606 : certificate2606.Sound := rat_cut_bin_certificate_sound certificate2606 profilesValid2606 numericValid2606 valid2606

def retention2607 : RatCutRetentionCertificate := ⟨(61/1000),(123/2000),(472635610133228779/981346584868116744),(1633662508739373773/200000000000000000),(21/20),(536563470737650093772847427664023888679/522772002796599607360000000000000000000),false,MergedCutProfiles.Batch409.profile16375,(fun _ => MergedCutProfiles.Batch409.profile16375)⟩
theorem profilesValid2607 : retention2607.ProfilesValid := by
  exact MergedCutProfiles.Batch409.valid16375
theorem numericValid2607 : retention2607.NumericValid := by decide +kernel
def certificate2607 : RatCutBinCertificate := ⟨⟨retention2607,(2285611066785509667/1000000000000000000),(19343761517970331/100000000000000000),(2020094325706112533/125000000000000000),(190899570021150208329/500000000000000000),(498827001718728861/500000000000000000)⟩,(497571832670278607/500000000000000000),(390412139365694349/1000000000000000000),(242383019529087491/1000000000000000000),(206256078916969739/1000000000000000000)⟩
theorem valid2607 : certificate2607.Valid := by decide +kernel
theorem sound2607 : certificate2607.Sound := rat_cut_bin_certificate_sound certificate2607 profilesValid2607 numericValid2607 valid2607

def retention2608 : RatCutRetentionCertificate := ⟨(61/1000),(123/2000),(11686966602141017863/23552318036834801856),(1417906830399686337/125000000000000000),(21/20),(1139880294498862787818699234806495318599/1134325464319749069600000000000000000000),false,MergedCutProfiles.Batch409.profile16376,(fun _ => MergedCutProfiles.Batch409.profile16376)⟩
theorem profilesValid2608 : retention2608.ProfilesValid := by
  exact MergedCutProfiles.Batch409.valid16376
theorem numericValid2608 : retention2608.NumericValid := by decide +kernel
def certificate2608 : RatCutBinCertificate := ⟨⟨retention2608,(2285611066785509667/1000000000000000000),(19343761517970331/100000000000000000),(2020094325706112533/125000000000000000),(190899570021150208329/500000000000000000),(97617009190169059/100000000000000000)⟩,(497571832670278607/500000000000000000),(391175117577372429/1000000000000000000),(60416546027223383/250000000000000000),(6479480835769021/31250000000000000)⟩
theorem valid2608 : certificate2608.Valid := by decide +kernel
theorem sound2608 : certificate2608.Sound := rat_cut_bin_certificate_sound certificate2608 profilesValid2608 numericValid2608 valid2608

def retention2609 : RatCutRetentionCertificate := ⟨(61/1000),(123/2000),(1/2),(11686966602141017863/1000000000000000000),(21/20),(18659668800638283428585968280413160245511/18699146563425628580800000000000000000000),false,MergedCutProfiles.Batch409.profile16377,(fun _ => MergedCutProfiles.Batch409.profile16377)⟩
theorem profilesValid2609 : retention2609.ProfilesValid := by
  exact MergedCutProfiles.Batch409.valid16377
theorem numericValid2609 : retention2609.NumericValid := by decide +kernel
def certificate2609 : RatCutBinCertificate := ⟨⟨retention2609,(2285611066785509667/1000000000000000000),(19343761517970331/100000000000000000),(2020094325706112533/125000000000000000),(190899570021150208329/500000000000000000),(484580943670987543/500000000000000000)⟩,(497571832670278607/500000000000000000),(19670354962774927/50000000000000000),(119788857615595667/500000000000000000),(204616106880045051/1000000000000000000)⟩
theorem valid2609 : certificate2609.Valid := by decide +kernel
theorem sound2609 : certificate2609.Sound := rat_cut_bin_certificate_sound certificate2609 profilesValid2609 numericValid2609 valid2609

def retention2610 : RatCutRetentionCertificate := ⟨(61/1000),(123/2000),(3537022963072578179/7850772678944933952),(5081330861966520487/1000000000000000000),(21/20),(8667924198084618878836058767987253466911/8130129379146432779200000000000000000000),false,MergedCutProfiles.Batch409.profile16378,(fun _ => MergedCutProfiles.Batch409.profile16378)⟩
theorem profilesValid2610 : retention2610.ProfilesValid := by
  exact MergedCutProfiles.Batch409.valid16378
theorem numericValid2610 : retention2610.NumericValid := by decide +kernel
def certificate2610 : RatCutBinCertificate := ⟨⟨retention2610,(2537666829785509667/1000000000000000000),(19343761517970331/100000000000000000),(2020094325706112533/125000000000000000),(190899570021150208329/500000000000000000),(1034251768469300383/1000000000000000000)⟩,(994607435685057557/1000000000000000000),(55869069415161869/250000000000000000),(53892803774843/122070312500000),(72987074487755219/200000000000000000)⟩
theorem valid2610 : certificate2610.Valid := by decide +kernel
theorem sound2610 : certificate2610.Sound := rat_cut_bin_certificate_sound certificate2610 profilesValid2610 numericValid2610 valid2610

def retention2611 : RatCutRetentionCertificate := ⟨(61/1000),(123/2000),(1450646221447079567/2944039754604350232),(10611068889217734537/1000000000000000000),1,(42098073025270330750577650306413012467/42444275556870938148000000000000000000),false,MergedCutProfiles.Batch409.profile16379,(fun _ => MergedCutProfiles.Batch409.profile16379)⟩
theorem profilesValid2611 : retention2611.ProfilesValid := by
  exact MergedCutProfiles.Batch409.valid16379
theorem numericValid2611 : retention2611.NumericValid := by decide +kernel
def certificate2611 : RatCutBinCertificate := ⟨⟨retention2611,(2537666829785509667/1000000000000000000),(19343761517970331/100000000000000000),(2020094325706112533/125000000000000000),(190899570021150208329/500000000000000000),(240366770062423199/250000000000000000)⟩,(994607435685057557/1000000000000000000),(120196905400773813/500000000000000000),(208411010250422193/500000000000000000),(365384017659262821/1000000000000000000)⟩
theorem valid2611 : certificate2611.Valid := by decide +kernel
theorem sound2611 : certificate2611.Sound := rat_cut_bin_certificate_sound certificate2611 profilesValid2611 numericValid2611 valid2611

def retention2612 : RatCutRetentionCertificate := ⟨(61/1000),(123/2000),(1953536911548733817/3925386339472466976),(1450646221447079567/125000000000000000),1,(2284996673913207568907337807757977363/2321033954315327307200000000000000000),false,MergedCutProfiles.Batch409.profile16380,(fun _ => MergedCutProfiles.Batch409.profile16380)⟩
theorem profilesValid2612 : retention2612.ProfilesValid := by
  exact MergedCutProfiles.Batch409.valid16380
theorem numericValid2612 : retention2612.NumericValid := by decide +kernel
def certificate2612 : RatCutBinCertificate := ⟨⟨retention2612,(2537666829785509667/1000000000000000000),(19343761517970331/100000000000000000),(2020094325706112533/125000000000000000),(190899570021150208329/500000000000000000),(954097450214505519/1000000000000000000)⟩,(994607435685057557/1000000000000000000),(121125329141953453/500000000000000000),(414187260354994711/1000000000000000000),(181547305583414463/500000000000000000)⟩
theorem valid2612 : certificate2612.Valid := by decide +kernel
theorem sound2612 : certificate2612.Sound := rat_cut_bin_certificate_sound certificate2612 profilesValid2612 numericValid2612 valid2612

def retention2613 : RatCutRetentionCertificate := ⟨(61/1000),(123/2000),(1/2),(5860610734646201451/500000000000000000),1,(15319097812133106749458335700528945797/15628295292389870536000000000000000000),false,MergedCutProfiles.Batch409.profile16377,(fun _ => MergedCutProfiles.Batch409.profile16377)⟩
theorem profilesValid2613 : retention2613.ProfilesValid := by
  exact MergedCutProfiles.Batch409.valid16377
theorem numericValid2613 : retention2613.NumericValid := by decide +kernel
def certificate2613 : RatCutBinCertificate := ⟨⟨retention2613,(2537666829785509667/1000000000000000000),(19343761517970331/100000000000000000),(2020094325706112533/125000000000000000),(190899570021150208329/500000000000000000),(949839387998100541/1000000000000000000)⟩,(994607435685057557/1000000000000000000),(243336650703227383/1000000000000000000),(103163199796522147/250000000000000000),(72105593079672843/200000000000000000)⟩
theorem valid2613 : certificate2613.Valid := by decide +kernel
theorem sound2613 : certificate2613.Sound := rat_cut_bin_certificate_sound certificate2613 profilesValid2613 numericValid2613 valid2613

def retention2614 : RatCutRetentionCertificate := ⟨(123/2000),(31/500),(936238362737414775/23102356905764287544),(926968675977638391/1000000000000000000),(53/20),(533708926635680691659/256000000000000000000),true,MergedCutProfiles.Batch409.profile16381,![MergedCutProfiles.Batch409.profile16381,MergedCutProfiles.Batch409.profile16382,MergedCutProfiles.Batch409.profile16383,MergedCutProfiles.Batch409.profile16384,MergedCutProfiles.Batch409.profile16385,MergedCutProfiles.Batch409.profile16386,MergedCutProfiles.Batch409.profile16387,MergedCutProfiles.Batch409.profile16388,MergedCutProfiles.Batch409.profile16389,MergedCutProfiles.Batch409.profile16390,MergedCutProfiles.Batch409.profile16391,MergedCutProfiles.Batch409.profile16392,MergedCutProfiles.Batch409.profile16393,MergedCutProfiles.Batch409.profile16394,MergedCutProfiles.Batch409.profile16395,MergedCutProfiles.Batch409.profile16396]⟩
theorem profilesValid2614 : retention2614.ProfilesValid := by
  change ∀ j : Fin 16, (retention2614.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch409.valid16381
  · exact MergedCutProfiles.Batch409.valid16382
  · exact MergedCutProfiles.Batch409.valid16383
  · exact MergedCutProfiles.Batch409.valid16384
  · exact MergedCutProfiles.Batch409.valid16385
  · exact MergedCutProfiles.Batch409.valid16386
  · exact MergedCutProfiles.Batch409.valid16387
  · exact MergedCutProfiles.Batch409.valid16388
  · exact MergedCutProfiles.Batch409.valid16389
  · exact MergedCutProfiles.Batch409.valid16390
  · exact MergedCutProfiles.Batch409.valid16391
  · exact MergedCutProfiles.Batch409.valid16392
  · exact MergedCutProfiles.Batch409.valid16393
  · exact MergedCutProfiles.Batch409.valid16394
  · exact MergedCutProfiles.Batch409.valid16395
  · exact MergedCutProfiles.Batch409.valid16396
theorem numericValid2614 : retention2614.NumericValid := by decide +kernel
def certificate2614 : RatCutBinCertificate := ⟨⟨retention2614,(1147499597416809633/500000000000000000),(24651154762240763/125000000000000000),(8155537656678971133/500000000000000000),(94498107574152091661/250000000000000000),(1005626718456064767/500000000000000000)⟩,(62193564122656627/62500000000000000),(296016538890354619/1000000000000000000),(68721022200611831/200000000000000000),(9902809667950461/50000000000000000)⟩
theorem valid2614 : certificate2614.Valid := by decide +kernel
theorem sound2614 : certificate2614.Sound := rat_cut_bin_certificate_sound certificate2614 profilesValid2614 numericValid2614 valid2614

def retention2615 : RatCutRetentionCertificate := ⟨(123/2000),(31/500),(121719491375000000/2887794613220535943),(37449534509496591/40000000000000000),(53/20),(16677042565697823987/8000000000000000000),true,MergedCutProfiles.Batch409.profile16397,![MergedCutProfiles.Batch409.profile16397,MergedCutProfiles.Batch409.profile16398,MergedCutProfiles.Batch409.profile16399,MergedCutProfiles.Batch410.profile16400,MergedCutProfiles.Batch410.profile16401,MergedCutProfiles.Batch410.profile16402,MergedCutProfiles.Batch410.profile16403,MergedCutProfiles.Batch410.profile16404,MergedCutProfiles.Batch410.profile16405,MergedCutProfiles.Batch410.profile16406,MergedCutProfiles.Batch410.profile16407,MergedCutProfiles.Batch410.profile16408,MergedCutProfiles.Batch410.profile16409,MergedCutProfiles.Batch410.profile16410,MergedCutProfiles.Batch410.profile16411,MergedCutProfiles.Batch410.profile16412]⟩
theorem profilesValid2615 : retention2615.ProfilesValid := by
  change ∀ j : Fin 16, (retention2615.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch409.valid16397
  · exact MergedCutProfiles.Batch409.valid16398
  · exact MergedCutProfiles.Batch409.valid16399
  · exact MergedCutProfiles.Batch410.valid16400
  · exact MergedCutProfiles.Batch410.valid16401
  · exact MergedCutProfiles.Batch410.valid16402
  · exact MergedCutProfiles.Batch410.valid16403
  · exact MergedCutProfiles.Batch410.valid16404
  · exact MergedCutProfiles.Batch410.valid16405
  · exact MergedCutProfiles.Batch410.valid16406
  · exact MergedCutProfiles.Batch410.valid16407
  · exact MergedCutProfiles.Batch410.valid16408
  · exact MergedCutProfiles.Batch410.valid16409
  · exact MergedCutProfiles.Batch410.valid16410
  · exact MergedCutProfiles.Batch410.valid16411
  · exact MergedCutProfiles.Batch410.valid16412
theorem numericValid2615 : retention2615.NumericValid := by decide +kernel
def certificate2615 : RatCutBinCertificate := ⟨⟨retention2615,(1147499597416809633/500000000000000000),(24651154762240763/125000000000000000),(8155537656678971133/500000000000000000),(94498107574152091661/250000000000000000),(2011083417580583757/1000000000000000000)⟩,(62193564122656627/62500000000000000),(73718423755408241/250000000000000000),(68999551727246463/200000000000000000),(99656667247271/500000000000000)⟩
theorem valid2615 : certificate2615.Valid := by decide +kernel
theorem sound2615 : certificate2615.Sound := rat_cut_bin_certificate_sound certificate2615 profilesValid2615 numericValid2615 valid2615

def certificates : List RatCutBinCertificate := [certificate2604,certificate2605,certificate2606,certificate2607,certificate2608,certificate2609,certificate2610,certificate2611,certificate2612,certificate2613,certificate2614,certificate2615]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound2604,List.forall_mem_cons.mpr ⟨sound2605,List.forall_mem_cons.mpr ⟨sound2606,List.forall_mem_cons.mpr ⟨sound2607,List.forall_mem_cons.mpr ⟨sound2608,List.forall_mem_cons.mpr ⟨sound2609,List.forall_mem_cons.mpr ⟨sound2610,List.forall_mem_cons.mpr ⟨sound2611,List.forall_mem_cons.mpr ⟨sound2612,List.forall_mem_cons.mpr ⟨sound2613,List.forall_mem_cons.mpr ⟨sound2614,List.forall_mem_cons.mpr ⟨sound2615,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch217
