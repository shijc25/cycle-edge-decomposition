import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch007
import Cycle12.MergedCutProfiles.Batch008
import Cycle12.MergedCutProfiles.Batch009
import Cycle12.MergedCutProfiles.Batch010
import Cycle12.MergedCutProfiles.Batch309
import Cycle12.MergedCutProfiles.Batch310
import Cycle12.MergedCutProfiles.Batch311

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch164

def retention1968 : RatCutRetentionCertificate := ⟨(7/1000),(1/125),(1178756187190861429/614213302476857892387),(1303852909/1000000000),(12/5),(36957483939140392547/16000000000000000000),true,MergedCutProfiles.Batch007.profile299,![MergedCutProfiles.Batch007.profile299,MergedCutProfiles.Batch007.profile302,MergedCutProfiles.Batch007.profile315,MergedCutProfiles.Batch309.profile12389,MergedCutProfiles.Batch007.profile311,MergedCutProfiles.Batch309.profile12388,MergedCutProfiles.Batch309.profile12390,MergedCutProfiles.Batch008.profile321,MergedCutProfiles.Batch008.profile333,MergedCutProfiles.Batch008.profile334,MergedCutProfiles.Batch309.profile12391,MergedCutProfiles.Batch309.profile12392,MergedCutProfiles.Batch309.profile12393,MergedCutProfiles.Batch309.profile12394,MergedCutProfiles.Batch309.profile12395,MergedCutProfiles.Batch309.profile12396]⟩
theorem profilesValid1968 : retention1968.ProfilesValid := by
  change ∀ j : Fin 16, (retention1968.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch007.valid299
  · exact MergedCutProfiles.Batch007.valid302
  · exact MergedCutProfiles.Batch007.valid315
  · exact MergedCutProfiles.Batch309.valid12389
  · exact MergedCutProfiles.Batch007.valid311
  · exact MergedCutProfiles.Batch309.valid12388
  · exact MergedCutProfiles.Batch309.valid12390
  · exact MergedCutProfiles.Batch008.valid321
  · exact MergedCutProfiles.Batch008.valid333
  · exact MergedCutProfiles.Batch008.valid334
  · exact MergedCutProfiles.Batch309.valid12391
  · exact MergedCutProfiles.Batch309.valid12392
  · exact MergedCutProfiles.Batch309.valid12393
  · exact MergedCutProfiles.Batch309.valid12394
  · exact MergedCutProfiles.Batch309.valid12395
  · exact MergedCutProfiles.Batch309.valid12396
theorem numericValid1968 : retention1968.NumericValid := by decide +kernel
def certificate1968 : RatCutBinCertificate := ⟨⟨retention1968,(910533507816089251/500000000000000000),(1291114465089419/500000000000000000),(7254878385114165641/1000000000000000000),(1342765598892166014881/100000000000000000),(1154143566170838227/500000000000000000)⟩,(999864646610345067/1000000000000000000),(42710037966935943/125000000000000000),(72847196010790661/250000000000000000),(2679177870523897/12500000000000000)⟩
theorem valid1968 : certificate1968.Valid := by decide +kernel
theorem sound1968 : certificate1968.Sound := rat_cut_bin_certificate_sound certificate1968 profilesValid1968 numericValid1968 valid1968

def retention1969 : RatCutRetentionCertificate := ⟨(7/1000),(1/125),(64000000000000000000/1842639907430573677161),(3536268561572584287/1000000000000000000),(27/20),(664645002635171857533/320000000000000000000),true,MergedCutProfiles.Batch309.profile12397,![MergedCutProfiles.Batch309.profile12397,MergedCutProfiles.Batch309.profile12398,MergedCutProfiles.Batch008.profile341,MergedCutProfiles.Batch309.profile12399,MergedCutProfiles.Batch310.profile12400,MergedCutProfiles.Batch310.profile12401,MergedCutProfiles.Batch310.profile12402,MergedCutProfiles.Batch310.profile12403,MergedCutProfiles.Batch310.profile12404,MergedCutProfiles.Batch310.profile12405,MergedCutProfiles.Batch310.profile12406,MergedCutProfiles.Batch310.profile12407,MergedCutProfiles.Batch310.profile12408,MergedCutProfiles.Batch310.profile12409,MergedCutProfiles.Batch310.profile12410,MergedCutProfiles.Batch310.profile12411]⟩
theorem profilesValid1969 : retention1969.ProfilesValid := by
  change ∀ j : Fin 16, (retention1969.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch309.valid12397
  · exact MergedCutProfiles.Batch309.valid12398
  · exact MergedCutProfiles.Batch008.valid341
  · exact MergedCutProfiles.Batch309.valid12399
  · exact MergedCutProfiles.Batch310.valid12400
  · exact MergedCutProfiles.Batch310.valid12401
  · exact MergedCutProfiles.Batch310.valid12402
  · exact MergedCutProfiles.Batch310.valid12403
  · exact MergedCutProfiles.Batch310.valid12404
  · exact MergedCutProfiles.Batch310.valid12405
  · exact MergedCutProfiles.Batch310.valid12406
  · exact MergedCutProfiles.Batch310.valid12407
  · exact MergedCutProfiles.Batch310.valid12408
  · exact MergedCutProfiles.Batch310.valid12409
  · exact MergedCutProfiles.Batch310.valid12410
  · exact MergedCutProfiles.Batch310.valid12411
theorem numericValid1969 : retention1969.NumericValid := by decide +kernel
def certificate1969 : RatCutBinCertificate := ⟨⟨retention1969,(910533507816089251/500000000000000000),(1291114465089419/500000000000000000),(7254878385114165641/1000000000000000000),(1342765598892166014881/100000000000000000),(129758787528764189/62500000000000000)⟩,(999864646610345067/1000000000000000000),(52820277818872541/200000000000000000),(76841810685670201/200000000000000000),(446837260547115863/1000000000000000000)⟩
theorem valid1969 : certificate1969.Valid := by decide +kernel
theorem sound1969 : certificate1969.Sound := rat_cut_bin_certificate_sound certificate1969 profilesValid1969 numericValid1969 valid1969

def retention1970 : RatCutRetentionCertificate := ⟨(7/1000),(1/125),(1/2),64,1,(255368898673698792760224881759734912191/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch008.profile355,(fun _ => MergedCutProfiles.Batch008.profile355)⟩
theorem profilesValid1970 : retention1970.ProfilesValid := by
  exact MergedCutProfiles.Batch008.valid355
theorem numericValid1970 : retention1970.NumericValid := by decide +kernel
def certificate1970 : RatCutBinCertificate := ⟨⟨retention1970,(910533507816089251/500000000000000000),(1291114465089419/500000000000000000),(7254878385114165641/1000000000000000000),(1342765598892166014881/100000000000000000),(996886588042605621/1000000000000000000)⟩,(999864646610345067/1000000000000000000),(416969601176179973/1000000000000000000),(109144397190909341/500000000000000000),(107121176409642303/500000000000000000)⟩
theorem valid1970 : certificate1970.Valid := by decide +kernel
theorem sound1970 : certificate1970.Sound := rat_cut_bin_certificate_sound certificate1970 profilesValid1970 numericValid1970 valid1970

def retention1971 : RatCutRetentionCertificate := ⟨(7/1000),(1/125),(64000000000000000000/1842639907430573677161),(2363971914728149319/500000000000000000),(23/20),(3816772107802366813101586012300919801311/1891177531782519455200000000000000000000),false,MergedCutProfiles.Batch310.profile12412,(fun _ => MergedCutProfiles.Batch310.profile12412)⟩
theorem profilesValid1971 : retention1971.ProfilesValid := by
  exact MergedCutProfiles.Batch310.valid12412
theorem numericValid1971 : retention1971.NumericValid := by decide +kernel
def certificate1971 : RatCutBinCertificate := ⟨⟨retention1971,(1042549208816089251/500000000000000000),(1291114465089419/500000000000000000),(7254878385114165641/1000000000000000000),(1342765598892166014881/100000000000000000),(2017345266413485181/1000000000000000000)⟩,(999845022095779971/1000000000000000000),(4902755158412029/40000000000000000),(618202711431450983/1000000000000000000),(409893738592493403/500000000000000000)⟩
theorem valid1971 : certificate1971.Valid := by decide +kernel
theorem sound1971 : certificate1971.Sound := rat_cut_bin_certificate_sound certificate1971 profilesValid1971 numericValid1971 valid1971

def retention1972 : RatCutRetentionCertificate := ⟨(7/1000),(1/125),(1/2),64,1,(255368898673698792760224881759734912191/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch008.profile355,(fun _ => MergedCutProfiles.Batch008.profile355)⟩
theorem profilesValid1972 : retention1972.ProfilesValid := by
  exact MergedCutProfiles.Batch008.valid355
theorem numericValid1972 : retention1972.NumericValid := by decide +kernel
def certificate1972 : RatCutBinCertificate := ⟨⟨retention1972,(1042549208816089251/500000000000000000),(1291114465089419/500000000000000000),(7254878385114165641/1000000000000000000),(1342765598892166014881/100000000000000000),(996792611342986833/1000000000000000000)⟩,(999845022095779971/1000000000000000000),(248059370591671637/1000000000000000000),(81207010187906843/200000000000000000),(398463525740967807/1000000000000000000)⟩
theorem valid1972 : certificate1972.Valid := by decide +kernel
theorem sound1972 : certificate1972.Sound := rat_cut_bin_certificate_sound certificate1972 profilesValid1972 numericValid1972 valid1972

def retention1973 : RatCutRetentionCertificate := ⟨(1/125),(9/1000),(620944295149591047/1449422154413990634511),(289582977526709937/500000000000000000),4,(283448454784678996057/128000000000000000000),true,MergedCutProfiles.Batch310.profile12413,![MergedCutProfiles.Batch310.profile12413,MergedCutProfiles.Batch008.profile356,MergedCutProfiles.Batch310.profile12414,MergedCutProfiles.Batch009.profile372,MergedCutProfiles.Batch310.profile12415,MergedCutProfiles.Batch008.profile358,MergedCutProfiles.Batch310.profile12416,MergedCutProfiles.Batch008.profile359,MergedCutProfiles.Batch310.profile12417,MergedCutProfiles.Batch009.profile360,MergedCutProfiles.Batch310.profile12418,MergedCutProfiles.Batch009.profile361,MergedCutProfiles.Batch310.profile12419,MergedCutProfiles.Batch009.profile362,MergedCutProfiles.Batch009.profile363,MergedCutProfiles.Batch009.profile387]⟩
theorem profilesValid1973 : retention1973.ProfilesValid := by
  change ∀ j : Fin 16, (retention1973.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch310.valid12413
  · exact MergedCutProfiles.Batch008.valid356
  · exact MergedCutProfiles.Batch310.valid12414
  · exact MergedCutProfiles.Batch009.valid372
  · exact MergedCutProfiles.Batch310.valid12415
  · exact MergedCutProfiles.Batch008.valid358
  · exact MergedCutProfiles.Batch310.valid12416
  · exact MergedCutProfiles.Batch008.valid359
  · exact MergedCutProfiles.Batch310.valid12417
  · exact MergedCutProfiles.Batch009.valid360
  · exact MergedCutProfiles.Batch310.valid12418
  · exact MergedCutProfiles.Batch009.valid361
  · exact MergedCutProfiles.Batch310.valid12419
  · exact MergedCutProfiles.Batch009.valid362
  · exact MergedCutProfiles.Batch009.valid363
  · exact MergedCutProfiles.Batch009.valid387
theorem numericValid1973 : retention1973.NumericValid := by decide +kernel
def certificate1973 : RatCutBinCertificate := ⟨⟨retention1973,(456579797779840367/250000000000000000),(3278736788116277/1000000000000000000),(7343161777134540253/1000000000000000000),(10691004789939291771169/1000000000000000000),(1105589615760603729/500000000000000000)⟩,(499914806697008297/500000000000000000),(286947267823982901/500000000000000000),(26854074011838663/250000000000000000),(5991271220813763/125000000000000000)⟩
theorem valid1973 : certificate1973.Valid := by decide +kernel
theorem sound1973 : certificate1973.Sound := rat_cut_bin_certificate_sound certificate1973 profilesValid1973 numericValid1973 valid1973

def retention1974 : RatCutRetentionCertificate := ⟨(1/125),(9/1000),(1305711442000000000/1449422154413990634511),(620944295149591047/1000000000000000000),4,(1132728140568036435720816468767591683/496755436119672837600000000000000000),true,MergedCutProfiles.Batch310.profile12420,![MergedCutProfiles.Batch310.profile12420,MergedCutProfiles.Batch009.profile372,MergedCutProfiles.Batch310.profile12421,MergedCutProfiles.Batch009.profile373,MergedCutProfiles.Batch310.profile12422,MergedCutProfiles.Batch009.profile374,MergedCutProfiles.Batch310.profile12423,MergedCutProfiles.Batch009.profile375,MergedCutProfiles.Batch009.profile365,MergedCutProfiles.Batch009.profile376,MergedCutProfiles.Batch310.profile12424,MergedCutProfiles.Batch009.profile368,MergedCutProfiles.Batch009.profile369,MergedCutProfiles.Batch009.profile370,MergedCutProfiles.Batch009.profile371,MergedCutProfiles.Batch310.profile12425]⟩
theorem profilesValid1974 : retention1974.ProfilesValid := by
  change ∀ j : Fin 16, (retention1974.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch310.valid12420
  · exact MergedCutProfiles.Batch009.valid372
  · exact MergedCutProfiles.Batch310.valid12421
  · exact MergedCutProfiles.Batch009.valid373
  · exact MergedCutProfiles.Batch310.valid12422
  · exact MergedCutProfiles.Batch009.valid374
  · exact MergedCutProfiles.Batch310.valid12423
  · exact MergedCutProfiles.Batch009.valid375
  · exact MergedCutProfiles.Batch009.valid365
  · exact MergedCutProfiles.Batch009.valid376
  · exact MergedCutProfiles.Batch310.valid12424
  · exact MergedCutProfiles.Batch009.valid368
  · exact MergedCutProfiles.Batch009.valid369
  · exact MergedCutProfiles.Batch009.valid370
  · exact MergedCutProfiles.Batch009.valid371
  · exact MergedCutProfiles.Batch310.valid12425
theorem numericValid1974 : retention1974.NumericValid := by decide +kernel
def certificate1974 : RatCutBinCertificate := ⟨⟨retention1974,(456579797779840367/250000000000000000),(3278736788116277/1000000000000000000),(7343161777134540253/1000000000000000000),(10691004789939291771169/1000000000000000000),(2276991313601039677/1000000000000000000)⟩,(499914806697008297/500000000000000000),(531979938654131389/1000000000000000000),(132261173577384213/1000000000000000000),(2449563268480517/40000000000000000)⟩
theorem valid1974 : certificate1974.Valid := by decide +kernel
theorem sound1974 : certificate1974.Sound := rat_cut_bin_certificate_sound certificate1974 profilesValid1974 numericValid1974 valid1974

def retention1975 : RatCutRetentionCertificate := ⟨(1/125),(9/1000),(4322355954516450454/1449422154413990634511),(652855721/500000000),(12/5),(36758601069661410233/16000000000000000000),true,MergedCutProfiles.Batch310.profile12426,![MergedCutProfiles.Batch310.profile12426,MergedCutProfiles.Batch009.profile362,MergedCutProfiles.Batch009.profile376,MergedCutProfiles.Batch009.profile369,MergedCutProfiles.Batch310.profile12427,MergedCutProfiles.Batch009.profile380,MergedCutProfiles.Batch009.profile389,MergedCutProfiles.Batch009.profile390,MergedCutProfiles.Batch009.profile385,MergedCutProfiles.Batch310.profile12428,MergedCutProfiles.Batch310.profile12429,MergedCutProfiles.Batch310.profile12430,MergedCutProfiles.Batch310.profile12431,MergedCutProfiles.Batch310.profile12432,MergedCutProfiles.Batch310.profile12433,MergedCutProfiles.Batch009.profile397]⟩
theorem profilesValid1975 : retention1975.ProfilesValid := by
  change ∀ j : Fin 16, (retention1975.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch310.valid12426
  · exact MergedCutProfiles.Batch009.valid362
  · exact MergedCutProfiles.Batch009.valid376
  · exact MergedCutProfiles.Batch009.valid369
  · exact MergedCutProfiles.Batch310.valid12427
  · exact MergedCutProfiles.Batch009.valid380
  · exact MergedCutProfiles.Batch009.valid389
  · exact MergedCutProfiles.Batch009.valid390
  · exact MergedCutProfiles.Batch009.valid385
  · exact MergedCutProfiles.Batch310.valid12428
  · exact MergedCutProfiles.Batch310.valid12429
  · exact MergedCutProfiles.Batch310.valid12430
  · exact MergedCutProfiles.Batch310.valid12431
  · exact MergedCutProfiles.Batch310.valid12432
  · exact MergedCutProfiles.Batch310.valid12433
  · exact MergedCutProfiles.Batch009.valid397
theorem numericValid1975 : retention1975.NumericValid := by decide +kernel
def certificate1975 : RatCutBinCertificate := ⟨⟨retention1975,(456579797779840367/250000000000000000),(3278736788116277/1000000000000000000),(7343161777134540253/1000000000000000000),(10691004789939291771169/1000000000000000000),(459091094806185897/200000000000000000)⟩,(499914806697008297/500000000000000000),(345047105678535829/1000000000000000000),(143895220277996801/500000000000000000),(210848023456295759/1000000000000000000)⟩
theorem valid1975 : certificate1975.Valid := by decide +kernel
theorem sound1975 : certificate1975.Sound := rat_cut_bin_certificate_sound certificate1975 profilesValid1975 numericValid1975 valid1975

def retention1976 : RatCutRetentionCertificate := ⟨(1/125),(9/1000),(64000000000000000000/1449422154413990634511),(2161177977258225227/500000000000000000),(5/4),(140770011179815216873032959896375996519/69157695272263207264000000000000000000),true,MergedCutProfiles.Batch009.profile396,![MergedCutProfiles.Batch009.profile396,MergedCutProfiles.Batch010.profile400,MergedCutProfiles.Batch310.profile12434,MergedCutProfiles.Batch010.profile401,MergedCutProfiles.Batch310.profile12435,MergedCutProfiles.Batch010.profile402,MergedCutProfiles.Batch310.profile12436,MergedCutProfiles.Batch010.profile403,MergedCutProfiles.Batch310.profile12437,MergedCutProfiles.Batch010.profile404,MergedCutProfiles.Batch310.profile12438,MergedCutProfiles.Batch010.profile405,MergedCutProfiles.Batch310.profile12439,MergedCutProfiles.Batch010.profile406,MergedCutProfiles.Batch311.profile12440,MergedCutProfiles.Batch010.profile407]⟩
theorem profilesValid1976 : retention1976.ProfilesValid := by
  change ∀ j : Fin 16, (retention1976.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch009.valid396
  · exact MergedCutProfiles.Batch010.valid400
  · exact MergedCutProfiles.Batch310.valid12434
  · exact MergedCutProfiles.Batch010.valid401
  · exact MergedCutProfiles.Batch310.valid12435
  · exact MergedCutProfiles.Batch010.valid402
  · exact MergedCutProfiles.Batch310.valid12436
  · exact MergedCutProfiles.Batch010.valid403
  · exact MergedCutProfiles.Batch310.valid12437
  · exact MergedCutProfiles.Batch010.valid404
  · exact MergedCutProfiles.Batch310.valid12438
  · exact MergedCutProfiles.Batch010.valid405
  · exact MergedCutProfiles.Batch310.valid12439
  · exact MergedCutProfiles.Batch010.valid406
  · exact MergedCutProfiles.Batch311.valid12440
  · exact MergedCutProfiles.Batch010.valid407
theorem numericValid1976 : retention1976.NumericValid := by decide +kernel
def certificate1976 : RatCutBinCertificate := ⟨⟨retention1976,(456579797779840367/250000000000000000),(3278736788116277/1000000000000000000),(7343161777134540253/1000000000000000000),(10691004789939291771169/1000000000000000000),(1017236887837728911/500000000000000000)⟩,(499914806697008297/500000000000000000),(129442663909926571/500000000000000000),(9779929513408561/25000000000000000),(489216218353682039/1000000000000000000)⟩
theorem valid1976 : certificate1976.Valid := by decide +kernel
theorem sound1976 : certificate1976.Sound := rat_cut_bin_certificate_sound certificate1976 profilesValid1976 numericValid1976 valid1976

def retention1977 : RatCutRetentionCertificate := ⟨(1/125),(9/1000),(1/2),64,1,(249383750761872694322254949188936071/250000000000000000000000000000000000),false,MergedCutProfiles.Batch010.profile416,(fun _ => MergedCutProfiles.Batch010.profile416)⟩
theorem profilesValid1977 : retention1977.ProfilesValid := by
  exact MergedCutProfiles.Batch010.valid416
theorem numericValid1977 : retention1977.NumericValid := by decide +kernel
def certificate1977 : RatCutBinCertificate := ⟨⟨retention1977,(456579797779840367/250000000000000000),(3278736788116277/1000000000000000000),(7343161777134540253/1000000000000000000),(10691004789939291771169/1000000000000000000),(996719547780509517/1000000000000000000)⟩,(499914806697008297/500000000000000000),(84196469508627077/200000000000000000),(21479801748977819/100000000000000000),(105387027082139567/500000000000000000)⟩
theorem valid1977 : certificate1977.Valid := by decide +kernel
theorem sound1977 : certificate1977.Sound := rat_cut_bin_certificate_sound certificate1977 profilesValid1977 numericValid1977 valid1977

def retention1978 : RatCutRetentionCertificate := ⟨(1/125),(9/1000),(64000000000000000000/1449422154413990634511),(2402239539803458241/500000000000000000),(23/20),(3818738813996774413176162428023577955231/1921791631842766592800000000000000000000),false,MergedCutProfiles.Batch311.profile12441,(fun _ => MergedCutProfiles.Batch311.profile12441)⟩
theorem profilesValid1978 : retention1978.ProfilesValid := by
  exact MergedCutProfiles.Batch311.valid12441
theorem numericValid1978 : retention1978.NumericValid := by decide +kernel
def certificate1978 : RatCutBinCertificate := ⟨⟨retention1978,(522947793029840367/250000000000000000),(3278736788116277/1000000000000000000),(7343161777134540253/1000000000000000000),(10691004789939291771169/1000000000000000000),(1985998158415244457/1000000000000000000)⟩,(199960969230041511/200000000000000000),(123215369976797123/1000000000000000000),(154219389986922591/250000000000000000),(202866160918936501/250000000000000000)⟩
theorem valid1978 : certificate1978.Valid := by decide +kernel
theorem sound1978 : certificate1978.Sound := rat_cut_bin_certificate_sound certificate1978 profilesValid1978 numericValid1978 valid1978

def retention1979 : RatCutRetentionCertificate := ⟨(1/125),(9/1000),(1/2),64,1,(249383750761872694322254949188936071/250000000000000000000000000000000000),false,MergedCutProfiles.Batch010.profile416,(fun _ => MergedCutProfiles.Batch010.profile416)⟩
theorem profilesValid1979 : retention1979.ProfilesValid := by
  exact MergedCutProfiles.Batch010.valid416
theorem numericValid1979 : retention1979.NumericValid := by decide +kernel
def certificate1979 : RatCutBinCertificate := ⟨⟨retention1979,(522947793029840367/250000000000000000),(3278736788116277/1000000000000000000),(7343161777134540253/1000000000000000000),(10691004789939291771169/1000000000000000000),(498300506998083047/500000000000000000)⟩,(199960969230041511/200000000000000000),(245540085175262993/1000000000000000000),(102388521239225131/250000000000000000),(200912301893297023/500000000000000000)⟩
theorem valid1979 : certificate1979.Valid := by decide +kernel
theorem sound1979 : certificate1979.Sound := rat_cut_bin_certificate_sound certificate1979 profilesValid1979 numericValid1979 valid1979

def certificates : List RatCutBinCertificate := [certificate1968,certificate1969,certificate1970,certificate1971,certificate1972,certificate1973,certificate1974,certificate1975,certificate1976,certificate1977,certificate1978,certificate1979]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound1968,List.forall_mem_cons.mpr ⟨sound1969,List.forall_mem_cons.mpr ⟨sound1970,List.forall_mem_cons.mpr ⟨sound1971,List.forall_mem_cons.mpr ⟨sound1972,List.forall_mem_cons.mpr ⟨sound1973,List.forall_mem_cons.mpr ⟨sound1974,List.forall_mem_cons.mpr ⟨sound1975,List.forall_mem_cons.mpr ⟨sound1976,List.forall_mem_cons.mpr ⟨sound1977,List.forall_mem_cons.mpr ⟨sound1978,List.forall_mem_cons.mpr ⟨sound1979,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch164
