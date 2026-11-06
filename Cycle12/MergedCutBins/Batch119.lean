import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch232
import Cycle12.MergedCutProfiles.Batch233
import Cycle12.MergedCutProfiles.Batch234

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch119

def retention1428 : RatCutRetentionCertificate := ⟨(61/1000),(49/800),(5917654145134479716/11890828153437861019),(1464765877508534583/250000000000000000),(11/10),(585174511871943943432723547361939377159/585906351003413833200000000000000000000),false,MergedCutProfiles.Batch232.profile9314,(fun _ => MergedCutProfiles.Batch232.profile9314)⟩
theorem profilesValid1428 : retention1428.ProfilesValid := by
  exact MergedCutProfiles.Batch232.valid9314
theorem numericValid1428 : retention1428.NumericValid := by decide +kernel
def certificate1428 : RatCutBinCertificate := ⟨⟨retention1428,(292104511969665911/125000000000000000),(191571141137618907/1000000000000000000),(16155495474611876117/1000000000000000000),(192398482326285571833/1000000000000000000),(968265111605480409/1000000000000000000)⟩,(495067365838166397/500000000000000000),(220453157774986957/500000000000000000),(39605009545630289/200000000000000000),(2370646015500897/15625000000000000)⟩
theorem valid1428 : certificate1428.Valid := by decide +kernel
theorem sound1428 : certificate1428.Sound := rat_cut_bin_certificate_sound certificate1428 profilesValid1428 numericValid1428 valid1428

def retention1429 : RatCutRetentionCertificate := ⟨(61/1000),(49/800),(1/2),(1479413536283619929/250000000000000000),(11/10),(36782545991390921872830733445424592061/36985338407090498225000000000000000000),false,MergedCutProfiles.Batch232.profile9315,(fun _ => MergedCutProfiles.Batch232.profile9315)⟩
theorem profilesValid1429 : retention1429.ProfilesValid := by
  exact MergedCutProfiles.Batch232.valid9315
theorem numericValid1429 : retention1429.NumericValid := by decide +kernel
def certificate1429 : RatCutBinCertificate := ⟨⟨retention1429,(292104511969665911/125000000000000000),(191571141137618907/1000000000000000000),(16155495474611876117/1000000000000000000),(192398482326285571833/1000000000000000000),(964031181274272389/1000000000000000000)⟩,(495067365838166397/500000000000000000),(8848761778215971/20000000000000000),(196773319292193601/1000000000000000000),(15036123530568693/100000000000000000)⟩
theorem valid1429 : certificate1429.Valid := by decide +kernel
theorem sound1429 : certificate1429.Sound := rat_cut_bin_certificate_sound certificate1429 profilesValid1429 numericValid1429 valid1429

def retention1430 : RatCutRetentionCertificate := ⟨(61/1000),(49/800),(1/2),64,1,(63852444837067109891680662227286171519/64000000000000000000000000000000000000),false,MergedCutProfiles.Batch232.profile9315,(fun _ => MergedCutProfiles.Batch232.profile9315)⟩
theorem profilesValid1430 : retention1430.ProfilesValid := by
  exact MergedCutProfiles.Batch232.valid9315
theorem numericValid1430 : retention1430.NumericValid := by decide +kernel
def certificate1430 : RatCutBinCertificate := ⟨⟨retention1430,(292104511969665911/125000000000000000),(191571141137618907/1000000000000000000),(16155495474611876117/1000000000000000000),(192398482326285571833/1000000000000000000),(60623995112518397/62500000000000000)⟩,(495067365838166397/500000000000000000),(80645063748331001/200000000000000000),(57635031837263047/250000000000000000),(54521882105156461/250000000000000000)⟩
theorem valid1430 : certificate1430.Valid := by decide +kernel
theorem sound1430 : certificate1430.Sound := rat_cut_bin_certificate_sound certificate1430 profilesValid1430 numericValid1430 valid1430

def retention1431 : RatCutRetentionCertificate := ⟨(61/1000),(49/800),(5575203713433261235/11890828153437861019),(3527585483698771833/1000000000000000000),(6/5),(124071566298791950819639787997716753517/117586182789959061100000000000000000000),false,MergedCutProfiles.Batch232.profile9316,(fun _ => MergedCutProfiles.Batch232.profile9316)⟩
theorem profilesValid1431 : retention1431.ProfilesValid := by
  exact MergedCutProfiles.Batch232.valid9316
theorem numericValid1431 : retention1431.NumericValid := by decide +kernel
def certificate1431 : RatCutBinCertificate := ⟨⟨retention1431,(332235580344665911/125000000000000000),(191571141137618907/1000000000000000000),(16155495474611876117/1000000000000000000),(192398482326285571833/1000000000000000000),(1017324910831232963/1000000000000000000)⟩,(988775822052180773/1000000000000000000),(96973985341170761/250000000000000000),(122378810742113473/500000000000000000),(170725671307214661/1000000000000000000)⟩
theorem valid1431 : certificate1431.Valid := by decide +kernel
theorem sound1431 : certificate1431.Sound := rat_cut_bin_certificate_sound certificate1431 profilesValid1431 numericValid1431 valid1431

def retention1432 : RatCutRetentionCertificate := ⟨(61/1000),(49/800),(5859595134173197936/11890828153437861019),(1115040742686652247/200000000000000000),(11/10),(1910575839767436209909294777423965297/1897941689679408080000000000000000000),false,MergedCutProfiles.Batch232.profile9317,(fun _ => MergedCutProfiles.Batch232.profile9317)⟩
theorem profilesValid1432 : retention1432.ProfilesValid := by
  exact MergedCutProfiles.Batch232.valid9317
theorem numericValid1432 : retention1432.NumericValid := by decide +kernel
def certificate1432 : RatCutBinCertificate := ⟨⟨retention1432,(332235580344665911/125000000000000000),(191571141137618907/1000000000000000000),(16155495474611876117/1000000000000000000),(192398482326285571833/1000000000000000000),(60748896917245067/62500000000000000)⟩,(988775822052180773/1000000000000000000),(202995560406115087/500000000000000000),(57009405788085713/250000000000000000),(173990581205530613/1000000000000000000)⟩
theorem valid1432 : certificate1432.Valid := by decide +kernel
theorem sound1432 : certificate1432.Sound := rat_cut_bin_certificate_sound certificate1432 profilesValid1432 numericValid1432 valid1432

def retention1433 : RatCutRetentionCertificate := ⟨(61/1000),(49/800),(5918191085514929916/11890828153437861019),(366224695885824871/62500000000000000),(21/20),(576875947615387207066433307656833197999/585959513417319793600000000000000000000),false,MergedCutProfiles.Batch232.profile9318,(fun _ => MergedCutProfiles.Batch232.profile9318)⟩
theorem profilesValid1433 : retention1433.ProfilesValid := by
  exact MergedCutProfiles.Batch232.valid9318
theorem numericValid1433 : retention1433.NumericValid := by decide +kernel
def certificate1433 : RatCutBinCertificate := ⟨⟨retention1433,(332235580344665911/125000000000000000),(191571141137618907/1000000000000000000),(16155495474611876117/1000000000000000000),(192398482326285571833/1000000000000000000),(237849919264093927/250000000000000000)⟩,(988775822052180773/1000000000000000000),(414774372408411221/1000000000000000000),(110107392820483659/500000000000000000),(171817559925548757/1000000000000000000)⟩
theorem valid1433 : certificate1433.Valid := by decide +kernel
theorem sound1433 : certificate1433.Sound := rat_cut_bin_certificate_sound certificate1433 profilesValid1433 numericValid1433 valid1433

def retention1434 : RatCutRetentionCertificate := ⟨(61/1000),(49/800),(1/2),(1479547771378732479/250000000000000000),(21/20),(193441151373313112837782086182278583493/197273036183830997200000000000000000000),false,MergedCutProfiles.Batch232.profile9315,(fun _ => MergedCutProfiles.Batch232.profile9315)⟩
theorem profilesValid1434 : retention1434.ProfilesValid := by
  exact MergedCutProfiles.Batch232.valid9315
theorem numericValid1434 : retention1434.NumericValid := by decide +kernel
def certificate1434 : RatCutBinCertificate := ⟨⟨retention1434,(332235580344665911/125000000000000000),(191571141137618907/1000000000000000000),(16155495474611876117/1000000000000000000),(192398482326285571833/1000000000000000000),(947477496179631007/1000000000000000000)⟩,(988775822052180773/1000000000000000000),(83298274745685059/200000000000000000),(109353691198603341/500000000000000000),(10640297635134753/62500000000000000)⟩
theorem valid1434 : certificate1434.Valid := by decide +kernel
theorem sound1434 : certificate1434.Sound := rat_cut_bin_certificate_sound certificate1434 profilesValid1434 numericValid1434 valid1434

def retention1435 : RatCutRetentionCertificate := ⟨(49/800),(123/2000),(201826041234146513/1962693169736233488),(880733450041343617/1000000000000000000),(13/5),(604977003415793641453/320000000000000000000),true,MergedCutProfiles.Batch232.profile9319,![MergedCutProfiles.Batch232.profile9319,MergedCutProfiles.Batch233.profile9320,MergedCutProfiles.Batch233.profile9321,MergedCutProfiles.Batch233.profile9322,MergedCutProfiles.Batch233.profile9323,MergedCutProfiles.Batch233.profile9324,MergedCutProfiles.Batch233.profile9325,MergedCutProfiles.Batch233.profile9326,MergedCutProfiles.Batch233.profile9327,MergedCutProfiles.Batch233.profile9328,MergedCutProfiles.Batch233.profile9329,MergedCutProfiles.Batch233.profile9330,MergedCutProfiles.Batch233.profile9331,MergedCutProfiles.Batch233.profile9332,MergedCutProfiles.Batch233.profile9333,MergedCutProfiles.Batch233.profile9334]⟩
theorem profilesValid1435 : retention1435.ProfilesValid := by
  change ∀ j : Fin 16, (retention1435.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch232.valid9319
  · exact MergedCutProfiles.Batch233.valid9320
  · exact MergedCutProfiles.Batch233.valid9321
  · exact MergedCutProfiles.Batch233.valid9322
  · exact MergedCutProfiles.Batch233.valid9323
  · exact MergedCutProfiles.Batch233.valid9324
  · exact MergedCutProfiles.Batch233.valid9325
  · exact MergedCutProfiles.Batch233.valid9326
  · exact MergedCutProfiles.Batch233.valid9327
  · exact MergedCutProfiles.Batch233.valid9328
  · exact MergedCutProfiles.Batch233.valid9329
  · exact MergedCutProfiles.Batch233.valid9330
  · exact MergedCutProfiles.Batch233.valid9331
  · exact MergedCutProfiles.Batch233.valid9332
  · exact MergedCutProfiles.Batch233.valid9333
  · exact MergedCutProfiles.Batch233.valid9334
theorem numericValid1435 : retention1435.NumericValid := by decide +kernel
def certificate1435 : RatCutBinCertificate := ⟨⟨retention1435,(1163558706285509667/500000000000000000),(19343761517970331/100000000000000000),(16230289452306054503/1000000000000000000),(38285146919970030553/200000000000000000),(363681903652149421/200000000000000000)⟩,(990148156725830789/1000000000000000000),(349496316413791767/1000000000000000000),(283085501687320437/1000000000000000000),(74927774678940087/500000000000000000)⟩
theorem valid1435 : certificate1435.Valid := by decide +kernel
theorem sound1435 : certificate1435.Sound := rat_cut_bin_certificate_sound certificate1435 profilesValid1435 numericValid1435 valid1435

def retention1436 : RatCutRetentionCertificate := ⟨(49/800),(123/2000),(868466315823838111/3925386339472466976),(605478123702439539/500000000000000000),(39/20),(1009648305053137084059/640000000000000000000),true,MergedCutProfiles.Batch233.profile9335,![MergedCutProfiles.Batch233.profile9335,MergedCutProfiles.Batch233.profile9336,MergedCutProfiles.Batch233.profile9337,MergedCutProfiles.Batch233.profile9338,MergedCutProfiles.Batch233.profile9339,MergedCutProfiles.Batch233.profile9340,MergedCutProfiles.Batch233.profile9341,MergedCutProfiles.Batch233.profile9342,MergedCutProfiles.Batch233.profile9343,MergedCutProfiles.Batch233.profile9344,MergedCutProfiles.Batch233.profile9345,MergedCutProfiles.Batch233.profile9346,MergedCutProfiles.Batch233.profile9347,MergedCutProfiles.Batch233.profile9348,MergedCutProfiles.Batch233.profile9349,MergedCutProfiles.Batch233.profile9350]⟩
theorem profilesValid1436 : retention1436.ProfilesValid := by
  change ∀ j : Fin 16, (retention1436.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch233.valid9335
  · exact MergedCutProfiles.Batch233.valid9336
  · exact MergedCutProfiles.Batch233.valid9337
  · exact MergedCutProfiles.Batch233.valid9338
  · exact MergedCutProfiles.Batch233.valid9339
  · exact MergedCutProfiles.Batch233.valid9340
  · exact MergedCutProfiles.Batch233.valid9341
  · exact MergedCutProfiles.Batch233.valid9342
  · exact MergedCutProfiles.Batch233.valid9343
  · exact MergedCutProfiles.Batch233.valid9344
  · exact MergedCutProfiles.Batch233.valid9345
  · exact MergedCutProfiles.Batch233.valid9346
  · exact MergedCutProfiles.Batch233.valid9347
  · exact MergedCutProfiles.Batch233.valid9348
  · exact MergedCutProfiles.Batch233.valid9349
  · exact MergedCutProfiles.Batch233.valid9350
theorem numericValid1436 : retention1436.NumericValid := by decide +kernel
def certificate1436 : RatCutBinCertificate := ⟨⟨retention1436,(1163558706285509667/500000000000000000),(19343761517970331/100000000000000000),(16230289452306054503/1000000000000000000),(38285146919970030553/200000000000000000),(1523468485816750813/1000000000000000000)⟩,(990148156725830789/1000000000000000000),(373163326418756311/1000000000000000000),(16187000816351887/62500000000000000),(150240584858488723/1000000000000000000)⟩
theorem valid1436 : certificate1436.Valid := by decide +kernel
theorem sound1436 : certificate1436.Sound := rat_cut_bin_certificate_sound certificate1436 profilesValid1436 numericValid1436 valid1436

def retention1437 : RatCutRetentionCertificate := ⟨(49/800),(123/2000),(4828357381606764263/11776159018417400928),(2605398947471514333/1000000000000000000),(6/5),(1475340733055145188193/1280000000000000000000),true,MergedCutProfiles.Batch233.profile9351,![MergedCutProfiles.Batch233.profile9351,MergedCutProfiles.Batch233.profile9352,MergedCutProfiles.Batch233.profile9353,MergedCutProfiles.Batch233.profile9354,MergedCutProfiles.Batch233.profile9355,MergedCutProfiles.Batch233.profile9356,MergedCutProfiles.Batch233.profile9357,MergedCutProfiles.Batch233.profile9358,MergedCutProfiles.Batch233.profile9359,MergedCutProfiles.Batch234.profile9360,MergedCutProfiles.Batch234.profile9361,MergedCutProfiles.Batch234.profile9362,MergedCutProfiles.Batch234.profile9363,MergedCutProfiles.Batch234.profile9364,MergedCutProfiles.Batch234.profile9365,MergedCutProfiles.Batch234.profile9366]⟩
theorem profilesValid1437 : retention1437.ProfilesValid := by
  change ∀ j : Fin 16, (retention1437.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch233.valid9351
  · exact MergedCutProfiles.Batch233.valid9352
  · exact MergedCutProfiles.Batch233.valid9353
  · exact MergedCutProfiles.Batch233.valid9354
  · exact MergedCutProfiles.Batch233.valid9355
  · exact MergedCutProfiles.Batch233.valid9356
  · exact MergedCutProfiles.Batch233.valid9357
  · exact MergedCutProfiles.Batch233.valid9358
  · exact MergedCutProfiles.Batch233.valid9359
  · exact MergedCutProfiles.Batch234.valid9360
  · exact MergedCutProfiles.Batch234.valid9361
  · exact MergedCutProfiles.Batch234.valid9362
  · exact MergedCutProfiles.Batch234.valid9363
  · exact MergedCutProfiles.Batch234.valid9364
  · exact MergedCutProfiles.Batch234.valid9365
  · exact MergedCutProfiles.Batch234.valid9366
theorem numericValid1437 : retention1437.NumericValid := by decide +kernel
def certificate1437 : RatCutBinCertificate := ⟨⟨retention1437,(1163558706285509667/500000000000000000),(19343761517970331/100000000000000000),(16230289452306054503/1000000000000000000),(38285146919970030553/200000000000000000),(559658411718690167/500000000000000000)⟩,(990148156725830789/1000000000000000000),(422424880702912887/1000000000000000000),(213552488949590189/1000000000000000000),(75837674090520657/500000000000000000)⟩
theorem valid1437 : certificate1437.Valid := by decide +kernel
theorem sound1437 : certificate1437.Sound := rat_cut_bin_certificate_sound certificate1437 profilesValid1437 numericValid1437 valid1437

def retention1438 : RatCutRetentionCertificate := ⟨(49/800),(123/2000),(1887209585243932253/3925386339472466976),(4828357381606764263/1000000000000000000),1,(254171089217960707223/256000000000000000000),true,MergedCutProfiles.Batch234.profile9367,![MergedCutProfiles.Batch234.profile9367,MergedCutProfiles.Batch234.profile9368,MergedCutProfiles.Batch233.profile9332,MergedCutProfiles.Batch234.profile9369,MergedCutProfiles.Batch234.profile9370,MergedCutProfiles.Batch234.profile9371,MergedCutProfiles.Batch234.profile9372,MergedCutProfiles.Batch234.profile9373,MergedCutProfiles.Batch234.profile9374,MergedCutProfiles.Batch234.profile9375,MergedCutProfiles.Batch234.profile9376,MergedCutProfiles.Batch234.profile9377,MergedCutProfiles.Batch234.profile9378,MergedCutProfiles.Batch234.profile9379,MergedCutProfiles.Batch234.profile9380,MergedCutProfiles.Batch234.profile9381]⟩
theorem profilesValid1438 : retention1438.ProfilesValid := by
  change ∀ j : Fin 16, (retention1438.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch234.valid9367
  · exact MergedCutProfiles.Batch234.valid9368
  · exact MergedCutProfiles.Batch233.valid9332
  · exact MergedCutProfiles.Batch234.valid9369
  · exact MergedCutProfiles.Batch234.valid9370
  · exact MergedCutProfiles.Batch234.valid9371
  · exact MergedCutProfiles.Batch234.valid9372
  · exact MergedCutProfiles.Batch234.valid9373
  · exact MergedCutProfiles.Batch234.valid9374
  · exact MergedCutProfiles.Batch234.valid9375
  · exact MergedCutProfiles.Batch234.valid9376
  · exact MergedCutProfiles.Batch234.valid9377
  · exact MergedCutProfiles.Batch234.valid9378
  · exact MergedCutProfiles.Batch234.valid9379
  · exact MergedCutProfiles.Batch234.valid9380
  · exact MergedCutProfiles.Batch234.valid9381
theorem numericValid1438 : retention1438.NumericValid := by decide +kernel
def certificate1438 : RatCutBinCertificate := ⟨⟨retention1438,(1163558706285509667/500000000000000000),(19343761517970331/100000000000000000),(16230289452306054503/1000000000000000000),(38285146919970030553/200000000000000000),(965114706749683267/1000000000000000000)⟩,(990148156725830789/1000000000000000000),(450283059768987743/1000000000000000000),(38089064784758981/200000000000000000),(151509172401394407/1000000000000000000)⟩
theorem valid1438 : certificate1438.Valid := by decide +kernel
theorem sound1438 : certificate1438.Sound := rat_cut_bin_certificate_sound certificate1438 profilesValid1438 numericValid1438 valid1438

def retention1439 : RatCutRetentionCertificate := ⟨(49/800),(123/2000),(2916590884329612967/5888079509208700464),(5661628755731796759/1000000000000000000),(11/10),(2269687045750919298020111155332104418359/2264651502292718703600000000000000000000),false,MergedCutProfiles.Batch234.profile9382,(fun _ => MergedCutProfiles.Batch234.profile9382)⟩
theorem profilesValid1439 : retention1439.ProfilesValid := by
  exact MergedCutProfiles.Batch234.valid9382
theorem numericValid1439 : retention1439.NumericValid := by decide +kernel
def certificate1439 : RatCutBinCertificate := ⟨⟨retention1439,(1163558706285509667/500000000000000000),(19343761517970331/100000000000000000),(16230289452306054503/1000000000000000000),(38285146919970030553/200000000000000000),(121463719166808679/125000000000000000)⟩,(990148156725830789/1000000000000000000),(440436321084912989/1000000000000000000),(198410181816445631/1000000000000000000),(7592549512709129/50000000000000000)⟩
theorem valid1439 : certificate1439.Valid := by decide +kernel
theorem sound1439 : certificate1439.Sound := rat_cut_bin_certificate_sound certificate1439 profilesValid1439 numericValid1439 valid1439

def certificates : List RatCutBinCertificate := [certificate1428,certificate1429,certificate1430,certificate1431,certificate1432,certificate1433,certificate1434,certificate1435,certificate1436,certificate1437,certificate1438,certificate1439]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound1428,List.forall_mem_cons.mpr ⟨sound1429,List.forall_mem_cons.mpr ⟨sound1430,List.forall_mem_cons.mpr ⟨sound1431,List.forall_mem_cons.mpr ⟨sound1432,List.forall_mem_cons.mpr ⟨sound1433,List.forall_mem_cons.mpr ⟨sound1434,List.forall_mem_cons.mpr ⟨sound1435,List.forall_mem_cons.mpr ⟨sound1436,List.forall_mem_cons.mpr ⟨sound1437,List.forall_mem_cons.mpr ⟨sound1438,List.forall_mem_cons.mpr ⟨sound1439,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch119
