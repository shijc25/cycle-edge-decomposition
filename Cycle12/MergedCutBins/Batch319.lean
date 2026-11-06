import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch025
import Cycle12.MergedCutProfiles.Batch026
import Cycle12.MergedCutProfiles.Batch027
import Cycle12.MergedCutProfiles.Batch028
import Cycle12.MergedCutProfiles.Batch320
import Cycle12.MergedCutProfiles.Batch321
import Cycle12.MergedCutProfiles.Batch322
import Cycle12.MergedCutProfiles.Batch323
import Cycle12.MergedCutProfiles.Batch456
import Cycle12.MergedCutProfiles.Batch457
import Cycle12.MergedCutProfiles.Batch582
import Cycle12.MergedCutProfiles.Batch583
import Cycle12.MergedCutProfiles.Batch584

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch319

def retention3828 : RatCutRetentionCertificate := ⟨(1/50),(21/1000),(61218225000000000/125904482924188692167),(574586604590540383/1000000000000000000),4,(253839143793197906010296186758170639/114917320918108076600000000000000000),true,MergedCutProfiles.Batch583.profile23325,![MergedCutProfiles.Batch583.profile23325,MergedCutProfiles.Batch456.profile18248,MergedCutProfiles.Batch583.profile23326,MergedCutProfiles.Batch456.profile18249,MergedCutProfiles.Batch320.profile12834,MergedCutProfiles.Batch456.profile18250,MergedCutProfiles.Batch583.profile23323,MergedCutProfiles.Batch456.profile18251,MergedCutProfiles.Batch583.profile23327,MergedCutProfiles.Batch321.profile12849,MergedCutProfiles.Batch025.profile1010,MergedCutProfiles.Batch321.profile12867,MergedCutProfiles.Batch456.profile18264,MergedCutProfiles.Batch456.profile18252,MergedCutProfiles.Batch583.profile23328,MergedCutProfiles.Batch456.profile18253]⟩
theorem profilesValid3828 : retention3828.ProfilesValid := by
  change ∀ j : Fin 16, (retention3828.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch583.valid23325
  · exact MergedCutProfiles.Batch456.valid18248
  · exact MergedCutProfiles.Batch583.valid23326
  · exact MergedCutProfiles.Batch456.valid18249
  · exact MergedCutProfiles.Batch320.valid12834
  · exact MergedCutProfiles.Batch456.valid18250
  · exact MergedCutProfiles.Batch583.valid23323
  · exact MergedCutProfiles.Batch456.valid18251
  · exact MergedCutProfiles.Batch583.valid23327
  · exact MergedCutProfiles.Batch321.valid12849
  · exact MergedCutProfiles.Batch025.valid1010
  · exact MergedCutProfiles.Batch321.valid12867
  · exact MergedCutProfiles.Batch456.valid18264
  · exact MergedCutProfiles.Batch456.valid18252
  · exact MergedCutProfiles.Batch583.valid23328
  · exact MergedCutProfiles.Batch456.valid18253
theorem numericValid3828 : retention3828.NumericValid := by decide +kernel
def certificate3828 : RatCutBinCertificate := ⟨⟨retention3828,(36270588668945551/20000000000000000),(1860584005120499/100000000000000000),(1709187668475437333/200000000000000000),(21622674815746229464277/1000000000000000000),(1096545813032871079/500000000000000000)⟩,(499958769251285331/500000000000000000),(676624335244220727/1000000000000000000),(14764943231614629/250000000000000000),(5228313817088401/200000000000000000)⟩
theorem valid3828 : certificate3828.Valid := by decide +kernel
theorem sound3828 : certificate3828.Sound := rat_cut_bin_certificate_sound certificate3828 profilesValid3828 numericValid3828 valid3828

def retention3829 : RatCutRetentionCertificate := ⟨(1/50),(21/1000),(1633427053166838951/2518089658483773843340),(2448729/2000000),(13/5),(723550733523070495289288325925233359/306091125000000000000000000000000000),true,MergedCutProfiles.Batch582.profile23315,![MergedCutProfiles.Batch582.profile23315,MergedCutProfiles.Batch582.profile23317,MergedCutProfiles.Batch456.profile18249,MergedCutProfiles.Batch583.profile23321,MergedCutProfiles.Batch583.profile23323,MergedCutProfiles.Batch456.profile18251,MergedCutProfiles.Batch583.profile23329,MergedCutProfiles.Batch320.profile12835,MergedCutProfiles.Batch321.profile12867,MergedCutProfiles.Batch583.profile23330,MergedCutProfiles.Batch583.profile23328,MergedCutProfiles.Batch456.profile18253,MergedCutProfiles.Batch456.profile18254,MergedCutProfiles.Batch583.profile23331,MergedCutProfiles.Batch321.profile12862,MergedCutProfiles.Batch025.profile1011]⟩
theorem profilesValid3829 : retention3829.ProfilesValid := by
  change ∀ j : Fin 16, (retention3829.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch582.valid23315
  · exact MergedCutProfiles.Batch582.valid23317
  · exact MergedCutProfiles.Batch456.valid18249
  · exact MergedCutProfiles.Batch583.valid23321
  · exact MergedCutProfiles.Batch583.valid23323
  · exact MergedCutProfiles.Batch456.valid18251
  · exact MergedCutProfiles.Batch583.valid23329
  · exact MergedCutProfiles.Batch320.valid12835
  · exact MergedCutProfiles.Batch321.valid12867
  · exact MergedCutProfiles.Batch583.valid23330
  · exact MergedCutProfiles.Batch583.valid23328
  · exact MergedCutProfiles.Batch456.valid18253
  · exact MergedCutProfiles.Batch456.valid18254
  · exact MergedCutProfiles.Batch583.valid23331
  · exact MergedCutProfiles.Batch321.valid12862
  · exact MergedCutProfiles.Batch025.valid1011
theorem numericValid3829 : retention3829.NumericValid := by decide +kernel
def certificate3829 : RatCutBinCertificate := ⟨⟨retention3829,(36270588668945551/20000000000000000),(1860584005120499/100000000000000000),(1709187668475437333/200000000000000000),(21622674815746229464277/1000000000000000000),(2353575265714037697/1000000000000000000)⟩,(499958769251285331/500000000000000000),(200772004646783297/500000000000000000),(14504414955925263/62500000000000000),(20443577017628909/125000000000000000)⟩
theorem valid3829 : certificate3829.Valid := by decide +kernel
theorem sound3829 : certificate3829.Sound := rat_cut_bin_certificate_sound certificate3829 profilesValid3829 numericValid3829 valid3829

def retention3830 : RatCutRetentionCertificate := ⟨(1/50),(21/1000),(3200000000000000000/125904482924188692167),(1633427053166838951/1000000000000000000),(43/20),(2772676673183787941847/1280000000000000000000),true,MergedCutProfiles.Batch321.profile12843,![MergedCutProfiles.Batch321.profile12843,MergedCutProfiles.Batch583.profile23332,MergedCutProfiles.Batch321.profile12861,MergedCutProfiles.Batch025.profile1034,MergedCutProfiles.Batch026.profile1044,MergedCutProfiles.Batch583.profile23333,MergedCutProfiles.Batch583.profile23334,MergedCutProfiles.Batch456.profile18278,MergedCutProfiles.Batch583.profile23335,MergedCutProfiles.Batch583.profile23336,MergedCutProfiles.Batch583.profile23337,MergedCutProfiles.Batch456.profile18279,MergedCutProfiles.Batch583.profile23338,MergedCutProfiles.Batch583.profile23339,MergedCutProfiles.Batch583.profile23340,MergedCutProfiles.Batch457.profile18280]⟩
theorem profilesValid3830 : retention3830.ProfilesValid := by
  change ∀ j : Fin 16, (retention3830.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch321.valid12843
  · exact MergedCutProfiles.Batch583.valid23332
  · exact MergedCutProfiles.Batch321.valid12861
  · exact MergedCutProfiles.Batch025.valid1034
  · exact MergedCutProfiles.Batch026.valid1044
  · exact MergedCutProfiles.Batch583.valid23333
  · exact MergedCutProfiles.Batch583.valid23334
  · exact MergedCutProfiles.Batch456.valid18278
  · exact MergedCutProfiles.Batch583.valid23335
  · exact MergedCutProfiles.Batch583.valid23336
  · exact MergedCutProfiles.Batch583.valid23337
  · exact MergedCutProfiles.Batch456.valid18279
  · exact MergedCutProfiles.Batch583.valid23338
  · exact MergedCutProfiles.Batch583.valid23339
  · exact MergedCutProfiles.Batch583.valid23340
  · exact MergedCutProfiles.Batch457.valid18280
theorem numericValid3830 : retention3830.NumericValid := by decide +kernel
def certificate3830 : RatCutBinCertificate := ⟨⟨retention3830,(36270588668945551/20000000000000000),(1860584005120499/100000000000000000),(1709187668475437333/200000000000000000),(21622674815746229464277/1000000000000000000),(1078832362900932297/500000000000000000)⟩,(499958769251285331/500000000000000000),(191349857781624321/500000000000000000),(249713179932648587/1000000000000000000),(194888138941950679/1000000000000000000)⟩
theorem valid3830 : certificate3830.Valid := by decide +kernel
theorem sound3830 : certificate3830.Sound := rat_cut_bin_certificate_sound certificate3830 profilesValid3830 numericValid3830 valid3830

def retention3831 : RatCutRetentionCertificate := ⟨(1/50),(21/1000),(1/2),64,1,(3990181166188230871926367807584118119/4000000000000000000000000000000000000),false,MergedCutProfiles.Batch026.profile1066,(fun _ => MergedCutProfiles.Batch026.profile1066)⟩
theorem profilesValid3831 : retention3831.ProfilesValid := by
  exact MergedCutProfiles.Batch026.valid1066
theorem numericValid3831 : retention3831.NumericValid := by decide +kernel
def certificate3831 : RatCutBinCertificate := ⟨⟨retention3831,(36270588668945551/20000000000000000),(1860584005120499/100000000000000000),(1709187668475437333/200000000000000000),(21622674815746229464277/1000000000000000000),(993596955194896539/1000000000000000000)⟩,(499958769251285331/500000000000000000),(480775958424459033/1000000000000000000),(167125793883421923/1000000000000000000),(8175174129473081/50000000000000000)⟩
theorem valid3831 : certificate3831.Valid := by decide +kernel
theorem sound3831 : certificate3831.Sound := rat_cut_bin_certificate_sound certificate3831 profilesValid3831 numericValid3831 valid3831

def retention3832 : RatCutRetentionCertificate := ⟨(1/50),(21/1000),(3200000000000000000/125904482924188692167),(3773723984721452401/200000000000000000),1,(159706882420121730062704712465392007539/75474479694429048020000000000000000000),false,MergedCutProfiles.Batch583.profile23341,(fun _ => MergedCutProfiles.Batch583.profile23341)⟩
theorem profilesValid3832 : retention3832.ProfilesValid := by
  exact MergedCutProfiles.Batch583.valid23341
theorem numericValid3832 : retention3832.NumericValid := by decide +kernel
def certificate3832 : RatCutBinCertificate := ⟨⟨retention3832,(35741950328945551/20000000000000000),(1860584005120499/100000000000000000),(1709187668475437333/200000000000000000),(21622674815746229464277/1000000000000000000),(132009213337082283/62500000000000000)⟩,(249979685092021181/250000000000000000),(6459509743004931/200000000000000000),(837602208267410089/1000000000000000000),(795453038527426419/500000000000000000)⟩
theorem valid3832 : certificate3832.Valid := by decide +kernel
theorem sound3832 : certificate3832.Sound := rat_cut_bin_certificate_sound certificate3832 profilesValid3832 numericValid3832 valid3832

def retention3833 : RatCutRetentionCertificate := ⟨(1/50),(21/1000),(1/2),64,1,(3990181166188230871926367807584118119/4000000000000000000000000000000000000),false,MergedCutProfiles.Batch026.profile1066,(fun _ => MergedCutProfiles.Batch026.profile1066)⟩
theorem profilesValid3833 : retention3833.ProfilesValid := by
  exact MergedCutProfiles.Batch026.valid1066
theorem numericValid3833 : retention3833.NumericValid := by decide +kernel
def certificate3833 : RatCutBinCertificate := ⟨⟨retention3833,(35741950328945551/20000000000000000),(1860584005120499/100000000000000000),(1709187668475437333/200000000000000000),(21622674815746229464277/1000000000000000000),(124206812699952041/125000000000000000)⟩,(249979685092021181/250000000000000000),(34326410169513541/500000000000000000),(370064307182417197/500000000000000000),(724129114274399203/1000000000000000000)⟩
theorem valid3833 : certificate3833.Valid := by decide +kernel
theorem sound3833 : certificate3833.Sound := rat_cut_bin_certificate_sound certificate3833 profilesValid3833 numericValid3833 valid3833

def retention3834 : RatCutRetentionCertificate := ⟨(21/1000),(11/500),(290331065285150582/1141678552781577970311),(558004894263574059/1000000000000000000),4,(1617070947573772209239234128263187557/744006525684765412000000000000000000),true,MergedCutProfiles.Batch583.profile23342,![MergedCutProfiles.Batch583.profile23342,MergedCutProfiles.Batch583.profile23343,MergedCutProfiles.Batch583.profile23344,MergedCutProfiles.Batch457.profile18294,MergedCutProfiles.Batch583.profile23345,MergedCutProfiles.Batch583.profile23346,MergedCutProfiles.Batch583.profile23347,MergedCutProfiles.Batch457.profile18295,MergedCutProfiles.Batch583.profile23348,MergedCutProfiles.Batch583.profile23349,MergedCutProfiles.Batch322.profile12888,MergedCutProfiles.Batch583.profile23350,MergedCutProfiles.Batch457.profile18296,MergedCutProfiles.Batch583.profile23351,MergedCutProfiles.Batch583.profile23352,MergedCutProfiles.Batch583.profile23353]⟩
theorem profilesValid3834 : retention3834.ProfilesValid := by
  change ∀ j : Fin 16, (retention3834.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch583.valid23342
  · exact MergedCutProfiles.Batch583.valid23343
  · exact MergedCutProfiles.Batch583.valid23344
  · exact MergedCutProfiles.Batch457.valid18294
  · exact MergedCutProfiles.Batch583.valid23345
  · exact MergedCutProfiles.Batch583.valid23346
  · exact MergedCutProfiles.Batch583.valid23347
  · exact MergedCutProfiles.Batch457.valid18295
  · exact MergedCutProfiles.Batch583.valid23348
  · exact MergedCutProfiles.Batch583.valid23349
  · exact MergedCutProfiles.Batch322.valid12888
  · exact MergedCutProfiles.Batch583.valid23350
  · exact MergedCutProfiles.Batch457.valid18296
  · exact MergedCutProfiles.Batch583.valid23351
  · exact MergedCutProfiles.Batch583.valid23352
  · exact MergedCutProfiles.Batch583.valid23353
theorem numericValid3834 : retention3834.NumericValid := by decide +kernel
def certificate3834 : RatCutBinCertificate := ⟨⟨retention3834,(36323955052895587/20000000000000000),(10247703429141591/500000000000000000),(541228170089349791/62500000000000000),(19868486828763672939793/1000000000000000000),(107813464548076039/50000000000000000)⟩,(19998205793007447/20000000000000000),(17640998148505991/25000000000000000),(24169289370184209/500000000000000000),(10493194654374879/500000000000000000)⟩
theorem valid3834 : certificate3834.Valid := by decide +kernel
theorem sound3834 : certificate3834.Sound := rat_cut_bin_certificate_sound certificate3834 profilesValid3834 numericValid3834 valid3834

def retention3835 : RatCutRetentionCertificate := ⟨(21/1000),(11/500),(612472330000000000/1141678552781577970311),(145165532642575291/250000000000000000),4,(142155569653359155411/64000000000000000000),true,MergedCutProfiles.Batch583.profile23343,![MergedCutProfiles.Batch583.profile23343,MergedCutProfiles.Batch457.profile18294,MergedCutProfiles.Batch583.profile23354,MergedCutProfiles.Batch457.profile18295,MergedCutProfiles.Batch583.profile23355,MergedCutProfiles.Batch457.profile18296,MergedCutProfiles.Batch583.profile23352,MergedCutProfiles.Batch457.profile18297,MergedCutProfiles.Batch583.profile23356,MergedCutProfiles.Batch322.profile12908,MergedCutProfiles.Batch026.profile1069,MergedCutProfiles.Batch457.profile18298,MergedCutProfiles.Batch583.profile23357,MergedCutProfiles.Batch323.profile12920,MergedCutProfiles.Batch583.profile23358,MergedCutProfiles.Batch457.profile18299]⟩
theorem profilesValid3835 : retention3835.ProfilesValid := by
  change ∀ j : Fin 16, (retention3835.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch583.valid23343
  · exact MergedCutProfiles.Batch457.valid18294
  · exact MergedCutProfiles.Batch583.valid23354
  · exact MergedCutProfiles.Batch457.valid18295
  · exact MergedCutProfiles.Batch583.valid23355
  · exact MergedCutProfiles.Batch457.valid18296
  · exact MergedCutProfiles.Batch583.valid23352
  · exact MergedCutProfiles.Batch457.valid18297
  · exact MergedCutProfiles.Batch583.valid23356
  · exact MergedCutProfiles.Batch322.valid12908
  · exact MergedCutProfiles.Batch026.valid1069
  · exact MergedCutProfiles.Batch457.valid18298
  · exact MergedCutProfiles.Batch583.valid23357
  · exact MergedCutProfiles.Batch323.valid12920
  · exact MergedCutProfiles.Batch583.valid23358
  · exact MergedCutProfiles.Batch457.valid18299
theorem numericValid3835 : retention3835.NumericValid := by decide +kernel
def certificate3835 : RatCutBinCertificate := ⟨⟨retention3835,(36323955052895587/20000000000000000),(10247703429141591/500000000000000000),(541228170089349791/62500000000000000),(19868486828763672939793/1000000000000000000),(440797334862779649/200000000000000000)⟩,(19998205793007447/20000000000000000),(335889950231256363/500000000000000000),(30484791132681167/500000000000000000),(27149748873932639/1000000000000000000)⟩
theorem valid3835 : certificate3835.Valid := by decide +kernel
theorem sound3835 : certificate3835.Sound := rat_cut_bin_certificate_sound certificate3835 profilesValid3835 numericValid3835 valid3835

def retention3836 : RatCutRetentionCertificate := ⟨(21/1000),(11/500),(764102869394018729/761119035187718646874),(61247233/50000000),(13/5),(2887217952063315999837146501102225159/1224944660000000000000000000000000000),true,MergedCutProfiles.Batch457.profile18294,![MergedCutProfiles.Batch457.profile18294,MergedCutProfiles.Batch583.profile23359,MergedCutProfiles.Batch583.profile23350,MergedCutProfiles.Batch583.profile23353,MergedCutProfiles.Batch322.profile12901,MergedCutProfiles.Batch026.profile1069,MergedCutProfiles.Batch583.profile23357,MergedCutProfiles.Batch583.profile23358,MergedCutProfiles.Batch584.profile23360,MergedCutProfiles.Batch027.profile1085,MergedCutProfiles.Batch457.profile18301,MergedCutProfiles.Batch457.profile18302,MergedCutProfiles.Batch457.profile18303,MergedCutProfiles.Batch322.profile12891,MergedCutProfiles.Batch322.profile12902,MergedCutProfiles.Batch322.profile12910]⟩
theorem profilesValid3836 : retention3836.ProfilesValid := by
  change ∀ j : Fin 16, (retention3836.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch457.valid18294
  · exact MergedCutProfiles.Batch583.valid23359
  · exact MergedCutProfiles.Batch583.valid23350
  · exact MergedCutProfiles.Batch583.valid23353
  · exact MergedCutProfiles.Batch322.valid12901
  · exact MergedCutProfiles.Batch026.valid1069
  · exact MergedCutProfiles.Batch583.valid23357
  · exact MergedCutProfiles.Batch583.valid23358
  · exact MergedCutProfiles.Batch584.valid23360
  · exact MergedCutProfiles.Batch027.valid1085
  · exact MergedCutProfiles.Batch457.valid18301
  · exact MergedCutProfiles.Batch457.valid18302
  · exact MergedCutProfiles.Batch457.valid18303
  · exact MergedCutProfiles.Batch322.valid12891
  · exact MergedCutProfiles.Batch322.valid12902
  · exact MergedCutProfiles.Batch322.valid12910
theorem numericValid3836 : retention3836.NumericValid := by decide +kernel
def certificate3836 : RatCutBinCertificate := ⟨⟨retention3836,(36323955052895587/20000000000000000),(10247703429141591/500000000000000000),(541228170089349791/62500000000000000),(19868486828763672939793/1000000000000000000),(586460732206303629/250000000000000000)⟩,(19998205793007447/20000000000000000),(202500537625600507/500000000000000000),(7154101491607841/31250000000000000),(160938677520321117/1000000000000000000)⟩
theorem valid3836 : certificate3836.Valid := by decide +kernel
theorem sound3836 : certificate3836.Sound := rat_cut_bin_certificate_sound certificate3836 profilesValid3836 numericValid3836 valid3836

def retention3837 : RatCutRetentionCertificate := ⟨(21/1000),(11/500),(32000000000000000000/1141678552781577970311),(2292308608182056187/1000000000000000000),(7/4),(549641236526634400671/256000000000000000000),true,MergedCutProfiles.Batch322.profile12895,![MergedCutProfiles.Batch322.profile12895,MergedCutProfiles.Batch027.profile1104,MergedCutProfiles.Batch027.profile1114,MergedCutProfiles.Batch027.profile1107,MergedCutProfiles.Batch027.profile1097,MergedCutProfiles.Batch027.profile1116,MergedCutProfiles.Batch584.profile23361,MergedCutProfiles.Batch584.profile23362,MergedCutProfiles.Batch584.profile23363,MergedCutProfiles.Batch584.profile23364,MergedCutProfiles.Batch584.profile23365,MergedCutProfiles.Batch028.profile1120,MergedCutProfiles.Batch584.profile23366,MergedCutProfiles.Batch584.profile23367,MergedCutProfiles.Batch028.profile1122,MergedCutProfiles.Batch584.profile23368]⟩
theorem profilesValid3837 : retention3837.ProfilesValid := by
  change ∀ j : Fin 16, (retention3837.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch322.valid12895
  · exact MergedCutProfiles.Batch027.valid1104
  · exact MergedCutProfiles.Batch027.valid1114
  · exact MergedCutProfiles.Batch027.valid1107
  · exact MergedCutProfiles.Batch027.valid1097
  · exact MergedCutProfiles.Batch027.valid1116
  · exact MergedCutProfiles.Batch584.valid23361
  · exact MergedCutProfiles.Batch584.valid23362
  · exact MergedCutProfiles.Batch584.valid23363
  · exact MergedCutProfiles.Batch584.valid23364
  · exact MergedCutProfiles.Batch584.valid23365
  · exact MergedCutProfiles.Batch028.valid1120
  · exact MergedCutProfiles.Batch584.valid23366
  · exact MergedCutProfiles.Batch584.valid23367
  · exact MergedCutProfiles.Batch028.valid1122
  · exact MergedCutProfiles.Batch584.valid23368
theorem numericValid3837 : retention3837.NumericValid := by decide +kernel
def certificate3837 : RatCutBinCertificate := ⟨⟨retention3837,(36323955052895587/20000000000000000),(10247703429141591/500000000000000000),(541228170089349791/62500000000000000),(19868486828763672939793/1000000000000000000),(2139513662173789689/1000000000000000000)⟩,(19998205793007447/20000000000000000),(339999885810551071/1000000000000000000),(73299283888396913/250000000000000000),(54940299978460931/200000000000000000)⟩
theorem valid3837 : certificate3837.Valid := by decide +kernel
theorem sound3837 : certificate3837.Sound := rat_cut_bin_certificate_sound certificate3837 profilesValid3837 numericValid3837 valid3837

def retention3838 : RatCutRetentionCertificate := ⟨(21/1000),(11/500),(1/2),64,1,(15960748357185807596877500066049185271/16000000000000000000000000000000000000),false,MergedCutProfiles.Batch028.profile1132,(fun _ => MergedCutProfiles.Batch028.profile1132)⟩
theorem profilesValid3838 : retention3838.ProfilesValid := by
  exact MergedCutProfiles.Batch028.valid1132
theorem numericValid3838 : retention3838.NumericValid := by decide +kernel
def certificate3838 : RatCutBinCertificate := ⟨⟨retention3838,(36323955052895587/20000000000000000),(10247703429141591/500000000000000000),(541228170089349791/62500000000000000),(19868486828763672939793/1000000000000000000),(248312062195991179/250000000000000000)⟩,(19998205793007447/20000000000000000),(96870565705875333/200000000000000000),(82259771678370111/500000000000000000),(160896919370806161/1000000000000000000)⟩
theorem valid3838 : certificate3838.Valid := by decide +kernel
theorem sound3838 : certificate3838.Sound := rat_cut_bin_certificate_sound certificate3838 profilesValid3838 numericValid3838 valid3838

def retention3839 : RatCutRetentionCertificate := ⟨(21/1000),(11/500),(32000000000000000000/1141678552781577970311),(19229017808784097583/1000000000000000000),1,(161916751813805763961283277767399195667/76916071235136390332000000000000000000),false,MergedCutProfiles.Batch584.profile23369,(fun _ => MergedCutProfiles.Batch584.profile23369)⟩
theorem profilesValid3839 : retention3839.ProfilesValid := by
  exact MergedCutProfiles.Batch584.valid23369
theorem numericValid3839 : retention3839.NumericValid := by decide +kernel
def certificate3839 : RatCutBinCertificate := ⟨⟨retention3839,(35754562252895587/20000000000000000),(10247703429141591/500000000000000000),(541228170089349791/62500000000000000),(19868486828763672939793/1000000000000000000),(1050439175805771673/500000000000000000)⟩,(199982339179804043/200000000000000000),(3205875449507053/100000000000000000),(419145589859709777/500000000000000000),(1587540324627202799/1000000000000000000)⟩
theorem valid3839 : certificate3839.Valid := by decide +kernel
theorem sound3839 : certificate3839.Sound := rat_cut_bin_certificate_sound certificate3839 profilesValid3839 numericValid3839 valid3839

def certificates : List RatCutBinCertificate := [certificate3828,certificate3829,certificate3830,certificate3831,certificate3832,certificate3833,certificate3834,certificate3835,certificate3836,certificate3837,certificate3838,certificate3839]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound3828,List.forall_mem_cons.mpr ⟨sound3829,List.forall_mem_cons.mpr ⟨sound3830,List.forall_mem_cons.mpr ⟨sound3831,List.forall_mem_cons.mpr ⟨sound3832,List.forall_mem_cons.mpr ⟨sound3833,List.forall_mem_cons.mpr ⟨sound3834,List.forall_mem_cons.mpr ⟨sound3835,List.forall_mem_cons.mpr ⟨sound3836,List.forall_mem_cons.mpr ⟨sound3837,List.forall_mem_cons.mpr ⟨sound3838,List.forall_mem_cons.mpr ⟨sound3839,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch319
