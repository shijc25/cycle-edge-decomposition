import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch249
import Cycle12.MergedCutProfiles.Batch250
import Cycle12.MergedCutProfiles.Batch251

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch129

def retention1548 : RatCutRetentionCertificate := ⟨(251/4000),(63/1000),(2722357304242923053/11117990995896675357),(319492543006227011/250000000000000000),(37/20),(486953419704937368503/320000000000000000000),true,MergedCutProfiles.Batch249.profile9975,![MergedCutProfiles.Batch249.profile9975,MergedCutProfiles.Batch249.profile9976,MergedCutProfiles.Batch249.profile9977,MergedCutProfiles.Batch249.profile9978,MergedCutProfiles.Batch249.profile9979,MergedCutProfiles.Batch249.profile9980,MergedCutProfiles.Batch249.profile9981,MergedCutProfiles.Batch249.profile9982,MergedCutProfiles.Batch249.profile9983,MergedCutProfiles.Batch249.profile9984,MergedCutProfiles.Batch249.profile9985,MergedCutProfiles.Batch249.profile9986,MergedCutProfiles.Batch249.profile9987,MergedCutProfiles.Batch249.profile9988,MergedCutProfiles.Batch249.profile9989,MergedCutProfiles.Batch249.profile9990]⟩
theorem profilesValid1548 : retention1548.ProfilesValid := by
  change ∀ j : Fin 16, (retention1548.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch249.valid9975
  · exact MergedCutProfiles.Batch249.valid9976
  · exact MergedCutProfiles.Batch249.valid9977
  · exact MergedCutProfiles.Batch249.valid9978
  · exact MergedCutProfiles.Batch249.valid9979
  · exact MergedCutProfiles.Batch249.valid9980
  · exact MergedCutProfiles.Batch249.valid9981
  · exact MergedCutProfiles.Batch249.valid9982
  · exact MergedCutProfiles.Batch249.valid9983
  · exact MergedCutProfiles.Batch249.valid9984
  · exact MergedCutProfiles.Batch249.valid9985
  · exact MergedCutProfiles.Batch249.valid9986
  · exact MergedCutProfiles.Batch249.valid9987
  · exact MergedCutProfiles.Batch249.valid9988
  · exact MergedCutProfiles.Batch249.valid9989
  · exact MergedCutProfiles.Batch249.valid9990
theorem numericValid1548 : retention1548.NumericValid := by decide +kernel
def certificate1548 : RatCutBinCertificate := ⟨⟨retention1548,(2350275959417506517/1000000000000000000),(204909449857824037/1000000000000000000),(4172562081220306441/250000000000000000),(92925823817745143157/500000000000000000),(1468323165285703769/1000000000000000000)⟩,(989893539807969717/1000000000000000000),(37034874297274151/100000000000000000),(32722105508271681/125000000000000000),(76830021065335279/500000000000000000)⟩
theorem valid1548 : certificate1548.Valid := by decide +kernel
theorem sound1548 : certificate1548.Sound := rat_cut_bin_certificate_sound certificate1548 profilesValid1548 numericValid1548 valid1548

def retention1549 : RatCutRetentionCertificate := ⟨(251/4000),(63/1000),(4705661498155406638/11117990995896675357),(2722357304242923053/1000000000000000000),(23/20),(1434161233115832342301/1280000000000000000000),true,MergedCutProfiles.Batch249.profile9991,![MergedCutProfiles.Batch249.profile9991,MergedCutProfiles.Batch249.profile9992,MergedCutProfiles.Batch249.profile9993,MergedCutProfiles.Batch249.profile9994,MergedCutProfiles.Batch249.profile9995,MergedCutProfiles.Batch249.profile9996,MergedCutProfiles.Batch249.profile9997,MergedCutProfiles.Batch249.profile9998,MergedCutProfiles.Batch249.profile9999,MergedCutProfiles.Batch250.profile10000,MergedCutProfiles.Batch250.profile10001,MergedCutProfiles.Batch250.profile10002,MergedCutProfiles.Batch250.profile10003,MergedCutProfiles.Batch250.profile10004,MergedCutProfiles.Batch250.profile10005,MergedCutProfiles.Batch250.profile10006]⟩
theorem profilesValid1549 : retention1549.ProfilesValid := by
  change ∀ j : Fin 16, (retention1549.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch249.valid9991
  · exact MergedCutProfiles.Batch249.valid9992
  · exact MergedCutProfiles.Batch249.valid9993
  · exact MergedCutProfiles.Batch249.valid9994
  · exact MergedCutProfiles.Batch249.valid9995
  · exact MergedCutProfiles.Batch249.valid9996
  · exact MergedCutProfiles.Batch249.valid9997
  · exact MergedCutProfiles.Batch249.valid9998
  · exact MergedCutProfiles.Batch249.valid9999
  · exact MergedCutProfiles.Batch250.valid10000
  · exact MergedCutProfiles.Batch250.valid10001
  · exact MergedCutProfiles.Batch250.valid10002
  · exact MergedCutProfiles.Batch250.valid10003
  · exact MergedCutProfiles.Batch250.valid10004
  · exact MergedCutProfiles.Batch250.valid10005
  · exact MergedCutProfiles.Batch250.valid10006
theorem numericValid1549 : retention1549.NumericValid := by decide +kernel
def certificate1549 : RatCutBinCertificate := ⟨⟨retention1549,(2350275959417506517/1000000000000000000),(204909449857824037/1000000000000000000),(4172562081220306441/250000000000000000),(92925823817745143157/500000000000000000),(67952734932569597/62500000000000000)⟩,(989893539807969717/1000000000000000000),(420880624132960243/1000000000000000000),(107443017503900043/500000000000000000),(77106957571992851/500000000000000000)⟩
theorem valid1549 : certificate1549.Valid := by decide +kernel
theorem sound1549 : certificate1549.Sound := rat_cut_bin_certificate_sound certificate1549 profilesValid1549 numericValid1549 valid1549

def retention1550 : RatCutRetentionCertificate := ⟨(251/4000),(63/1000),(5355481731044314028/11117990995896675357),(2352830749077703319/500000000000000000),1,(126861762459137559719/128000000000000000000),true,MergedCutProfiles.Batch250.profile10007,![MergedCutProfiles.Batch250.profile10007,MergedCutProfiles.Batch250.profile10008,MergedCutProfiles.Batch250.profile10009,MergedCutProfiles.Batch250.profile10010,MergedCutProfiles.Batch250.profile10011,MergedCutProfiles.Batch250.profile10012,MergedCutProfiles.Batch250.profile10013,MergedCutProfiles.Batch250.profile10014,MergedCutProfiles.Batch250.profile10015,MergedCutProfiles.Batch250.profile10016,MergedCutProfiles.Batch250.profile10017,MergedCutProfiles.Batch250.profile10018,MergedCutProfiles.Batch250.profile10019,MergedCutProfiles.Batch250.profile10020,MergedCutProfiles.Batch250.profile10021,MergedCutProfiles.Batch250.profile10022]⟩
theorem profilesValid1550 : retention1550.ProfilesValid := by
  change ∀ j : Fin 16, (retention1550.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch250.valid10007
  · exact MergedCutProfiles.Batch250.valid10008
  · exact MergedCutProfiles.Batch250.valid10009
  · exact MergedCutProfiles.Batch250.valid10010
  · exact MergedCutProfiles.Batch250.valid10011
  · exact MergedCutProfiles.Batch250.valid10012
  · exact MergedCutProfiles.Batch250.valid10013
  · exact MergedCutProfiles.Batch250.valid10014
  · exact MergedCutProfiles.Batch250.valid10015
  · exact MergedCutProfiles.Batch250.valid10016
  · exact MergedCutProfiles.Batch250.valid10017
  · exact MergedCutProfiles.Batch250.valid10018
  · exact MergedCutProfiles.Batch250.valid10019
  · exact MergedCutProfiles.Batch250.valid10020
  · exact MergedCutProfiles.Batch250.valid10021
  · exact MergedCutProfiles.Batch250.valid10022
theorem numericValid1550 : retention1550.NumericValid := by decide +kernel
def certificate1550 : RatCutBinCertificate := ⟨⟨retention1550,(2350275959417506517/1000000000000000000),(204909449857824037/1000000000000000000),(4172562081220306441/250000000000000000),(92925823817745143157/500000000000000000),(60140372493788827/62500000000000000)⟩,(989893539807969717/1000000000000000000),(442150900405398899/1000000000000000000),(197007598424832561/1000000000000000000),(38904050491247197/250000000000000000)⟩
theorem valid1550 : certificate1550.Valid := by decide +kernel
theorem sound1550 : certificate1550.Sound := rat_cut_bin_certificate_sound certificate1550 profilesValid1550 numericValid1550 valid1550

def retention1551 : RatCutRetentionCertificate := ⟨(251/4000),(63/1000),(5517758182976687789/11117990995896675357),(1338870432761078507/250000000000000000),(11/10),(534794174557993266614513468370507727159/535548173104431402800000000000000000000),false,MergedCutProfiles.Batch250.profile10023,(fun _ => MergedCutProfiles.Batch250.profile10023)⟩
theorem profilesValid1551 : retention1551.ProfilesValid := by
  exact MergedCutProfiles.Batch250.valid10023
theorem numericValid1551 : retention1551.NumericValid := by decide +kernel
def certificate1551 : RatCutBinCertificate := ⟨⟨retention1551,(2350275959417506517/1000000000000000000),(204909449857824037/1000000000000000000),(4172562081220306441/250000000000000000),(92925823817745143157/500000000000000000),(120855735080859661/125000000000000000)⟩,(989893539807969717/1000000000000000000),(108627605010185447/250000000000000000),(203309323703328003/1000000000000000000),(153778255694832439/1000000000000000000)⟩
theorem valid1551 : certificate1551.Valid := by decide +kernel
theorem sound1551 : certificate1551.Sound := rat_cut_bin_certificate_sound certificate1551 profilesValid1551 numericValid1551 valid1551

def retention1552 : RatCutRetentionCertificate := ⟨(251/4000),(63/1000),(1/2),(5517758182976687789/1000000000000000000),(11/10),(2190452045586285330941226576869011841479/2207103273190675115600000000000000000000),false,MergedCutProfiles.Batch250.profile10024,(fun _ => MergedCutProfiles.Batch250.profile10024)⟩
theorem profilesValid1552 : retention1552.ProfilesValid := by
  exact MergedCutProfiles.Batch250.valid10024
theorem numericValid1552 : retention1552.NumericValid := by decide +kernel
def certificate1552 : RatCutBinCertificate := ⟨⟨retention1552,(2350275959417506517/1000000000000000000),(204909449857824037/1000000000000000000),(4172562081220306441/250000000000000000),(92925823817745143157/500000000000000000),(960709575042579179/1000000000000000000)⟩,(989893539807969717/1000000000000000000),(109024756735058659/250000000000000000),(201988086949697991/1000000000000000000),(76258620525527213/500000000000000000)⟩
theorem valid1552 : certificate1552.Valid := by decide +kernel
theorem sound1552 : certificate1552.Sound := rat_cut_bin_certificate_sound certificate1552 profilesValid1552 numericValid1552 valid1552

def retention1553 : RatCutRetentionCertificate := ⟨(251/4000),(63/1000),(1/2),64,1,(40866013821036615395097175148919/40960000000000000000000000000000),false,MergedCutProfiles.Batch250.profile10024,(fun _ => MergedCutProfiles.Batch250.profile10024)⟩
theorem profilesValid1553 : retention1553.ProfilesValid := by
  exact MergedCutProfiles.Batch250.valid10024
theorem numericValid1553 : retention1553.NumericValid := by decide +kernel
def certificate1553 : RatCutBinCertificate := ⟨⟨retention1553,(2350275959417506517/1000000000000000000),(204909449857824037/1000000000000000000),(4172562081220306441/250000000000000000),(92925823817745143157/500000000000000000),(968850119872628583/1000000000000000000)⟩,(989893539807969717/1000000000000000000),(3969475002396991/10000000000000000),(236290887327042207/1000000000000000000),(223214884674821811/1000000000000000000)⟩
theorem valid1553 : certificate1553.Valid := by decide +kernel
theorem sound1553 : certificate1553.Sound := rat_cut_bin_certificate_sound certificate1553 profilesValid1553 numericValid1553 valid1553

def retention1554 : RatCutRetentionCertificate := ⟨(251/4000),(63/1000),(578567753900271357/1235332332877408373),(33276291042337749/10000000000000000),(6/5),(2002907496062587325171680430841542153/1901502345276442800000000000000000000),false,MergedCutProfiles.Batch250.profile10025,(fun _ => MergedCutProfiles.Batch250.profile10025)⟩
theorem profilesValid1554 : retention1554.ProfilesValid := by
  exact MergedCutProfiles.Batch250.valid10025
theorem numericValid1554 : retention1554.NumericValid := by decide +kernel
def certificate1554 : RatCutBinCertificate := ⟨⟨retention1554,(2670033259417506517/1000000000000000000),(204909449857824037/1000000000000000000),(4172562081220306441/250000000000000000),(92925823817745143157/500000000000000000),(253495369305862019/250000000000000000)⟩,(494257263548815723/500000000000000000),(96902757585236397/250000000000000000),(61256881396558451/250000000000000000),(168693094456774063/1000000000000000000)⟩
theorem valid1554 : certificate1554.Valid := by decide +kernel
theorem sound1554 : certificate1554.Sound := rat_cut_bin_certificate_sound certificate1554 profilesValid1554 numericValid1554 valid1554

def retention1555 : RatCutRetentionCertificate := ⟨(251/4000),(63/1000),(5527451963277885209/11117990995896675357),(5207109785102442213/1000000000000000000),(11/10),(76829339504071719235955499909341354493/77142367186702847600000000000000000000),false,MergedCutProfiles.Batch250.profile10026,(fun _ => MergedCutProfiles.Batch250.profile10026)⟩
theorem profilesValid1555 : retention1555.ProfilesValid := by
  exact MergedCutProfiles.Batch250.valid10026
theorem numericValid1555 : retention1555.NumericValid := by decide +kernel
def certificate1555 : RatCutBinCertificate := ⟨⟨retention1555,(2670033259417506517/1000000000000000000),(204909449857824037/1000000000000000000),(4172562081220306441/250000000000000000),(92925823817745143157/500000000000000000),(959876693291584073/1000000000000000000)⟩,(494257263548815723/500000000000000000),(409459264799362057/1000000000000000000),(224926239025721623/1000000000000000000),(168202427374485777/1000000000000000000)⟩
theorem valid1555 : certificate1555.Valid := by decide +kernel
theorem sound1555 : certificate1555.Sound := rat_cut_bin_certificate_sound certificate1555 profilesValid1555 numericValid1555 valid1555

def retention1556 : RatCutRetentionCertificate := ⟨(251/4000),(63/1000),(1/2),(5527451963277885209/1000000000000000000),(11/10),(2194422976896943989046864879025181576319/2210980785311154083600000000000000000000),false,MergedCutProfiles.Batch250.profile10024,(fun _ => MergedCutProfiles.Batch250.profile10024)⟩
theorem profilesValid1556 : retention1556.ProfilesValid := by
  exact MergedCutProfiles.Batch250.valid10024
theorem numericValid1556 : retention1556.NumericValid := by decide +kernel
def certificate1556 : RatCutBinCertificate := ⟨⟨retention1556,(2670033259417506517/1000000000000000000),(204909449857824037/1000000000000000000),(4172562081220306441/250000000000000000),(92925823817745143157/500000000000000000),(956445990105113391/1000000000000000000)⟩,(494257263548815723/500000000000000000),(410927965822744187/1000000000000000000),(1747011601917613/7812500000000000),(41999076712611473/250000000000000000)⟩
theorem valid1556 : certificate1556.Valid := by decide +kernel
theorem sound1556 : certificate1556.Sound := rat_cut_bin_certificate_sound certificate1556 profilesValid1556 numericValid1556 valid1556

def retention1557 : RatCutRetentionCertificate := ⟨(63/1000),(101/1600),(1446965980212557923/11065360034428862023),(915535368672746039/1000000000000000000),(5/2),(92900431776499799011/51200000000000000000),true,MergedCutProfiles.Batch250.profile10027,![MergedCutProfiles.Batch250.profile10027,MergedCutProfiles.Batch250.profile10028,MergedCutProfiles.Batch250.profile10029,MergedCutProfiles.Batch250.profile10030,MergedCutProfiles.Batch250.profile10031,MergedCutProfiles.Batch250.profile10032,MergedCutProfiles.Batch250.profile10033,MergedCutProfiles.Batch250.profile10034,MergedCutProfiles.Batch250.profile10035,MergedCutProfiles.Batch250.profile10036,MergedCutProfiles.Batch250.profile10037,MergedCutProfiles.Batch250.profile10038,MergedCutProfiles.Batch250.profile10039,MergedCutProfiles.Batch251.profile10040,MergedCutProfiles.Batch251.profile10041,MergedCutProfiles.Batch251.profile10042]⟩
theorem profilesValid1557 : retention1557.ProfilesValid := by
  change ∀ j : Fin 16, (retention1557.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch250.valid10027
  · exact MergedCutProfiles.Batch250.valid10028
  · exact MergedCutProfiles.Batch250.valid10029
  · exact MergedCutProfiles.Batch250.valid10030
  · exact MergedCutProfiles.Batch250.valid10031
  · exact MergedCutProfiles.Batch250.valid10032
  · exact MergedCutProfiles.Batch250.valid10033
  · exact MergedCutProfiles.Batch250.valid10034
  · exact MergedCutProfiles.Batch250.valid10035
  · exact MergedCutProfiles.Batch250.valid10036
  · exact MergedCutProfiles.Batch250.valid10037
  · exact MergedCutProfiles.Batch250.valid10038
  · exact MergedCutProfiles.Batch250.valid10039
  · exact MergedCutProfiles.Batch251.valid10040
  · exact MergedCutProfiles.Batch251.valid10041
  · exact MergedCutProfiles.Batch251.valid10042
theorem numericValid1557 : retention1557.NumericValid := by decide +kernel
def certificate1557 : RatCutBinCertificate := ⟨⟨retention1557,(235080847894458661/100000000000000000),(205886892695735953/1000000000000000000),(4192221140517765803/250000000000000000),(185698677009292092909/1000000000000000000),(435567263646454467/250000000000000000)⟩,(197981462140580407/200000000000000000),(171490832897774719/500000000000000000),(144997008200066299/500000000000000000),(153027523609538219/1000000000000000000)⟩
theorem valid1557 : certificate1557.Valid := by decide +kernel
theorem sound1557 : certificate1557.Sound := rat_cut_bin_certificate_sound certificate1557 profilesValid1557 numericValid1557 valid1557

def retention1558 : RatCutRetentionCertificate := ⟨(63/1000),(101/1600),(3144310858836958148/11065360034428862023),(1446965980212557923/1000000000000000000),(7/4),(368096312372594310439/256000000000000000000),true,MergedCutProfiles.Batch251.profile10043,![MergedCutProfiles.Batch251.profile10043,MergedCutProfiles.Batch251.profile10044,MergedCutProfiles.Batch251.profile10045,MergedCutProfiles.Batch251.profile10046,MergedCutProfiles.Batch251.profile10047,MergedCutProfiles.Batch251.profile10048,MergedCutProfiles.Batch251.profile10049,MergedCutProfiles.Batch251.profile10050,MergedCutProfiles.Batch251.profile10051,MergedCutProfiles.Batch251.profile10052,MergedCutProfiles.Batch251.profile10053,MergedCutProfiles.Batch251.profile10054,MergedCutProfiles.Batch251.profile10055,MergedCutProfiles.Batch251.profile10056,MergedCutProfiles.Batch251.profile10057,MergedCutProfiles.Batch251.profile10058]⟩
theorem profilesValid1558 : retention1558.ProfilesValid := by
  change ∀ j : Fin 16, (retention1558.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch251.valid10043
  · exact MergedCutProfiles.Batch251.valid10044
  · exact MergedCutProfiles.Batch251.valid10045
  · exact MergedCutProfiles.Batch251.valid10046
  · exact MergedCutProfiles.Batch251.valid10047
  · exact MergedCutProfiles.Batch251.valid10048
  · exact MergedCutProfiles.Batch251.valid10049
  · exact MergedCutProfiles.Batch251.valid10050
  · exact MergedCutProfiles.Batch251.valid10051
  · exact MergedCutProfiles.Batch251.valid10052
  · exact MergedCutProfiles.Batch251.valid10053
  · exact MergedCutProfiles.Batch251.valid10054
  · exact MergedCutProfiles.Batch251.valid10055
  · exact MergedCutProfiles.Batch251.valid10056
  · exact MergedCutProfiles.Batch251.valid10057
  · exact MergedCutProfiles.Batch251.valid10058
theorem numericValid1558 : retention1558.NumericValid := by decide +kernel
def certificate1558 : RatCutBinCertificate := ⟨⟨retention1558,(235080847894458661/100000000000000000),(205886892695735953/1000000000000000000),(4192221140517765803/250000000000000000),(185698677009292092909/1000000000000000000),(1387343819103266851/1000000000000000000)⟩,(197981462140580407/200000000000000000),(74768102884703847/200000000000000000),(64581288732831693/250000000000000000),(19260738317004021/125000000000000000)⟩
theorem valid1558 : certificate1558.Valid := by decide +kernel
theorem sound1558 : certificate1558.Sound := rat_cut_bin_certificate_sound certificate1558 profilesValid1558 numericValid1558 valid1558

def retention1559 : RatCutRetentionCertificate := ⟨(63/1000),(101/1600),(4920251424542041561/11065360034428862023),(786077714709239537/250000000000000000),(11/10),(344130994664737519481/320000000000000000000),true,MergedCutProfiles.Batch251.profile10059,![MergedCutProfiles.Batch251.profile10059,MergedCutProfiles.Batch251.profile10060,MergedCutProfiles.Batch251.profile10061,MergedCutProfiles.Batch251.profile10062,MergedCutProfiles.Batch251.profile10063,MergedCutProfiles.Batch251.profile10064,MergedCutProfiles.Batch251.profile10065,MergedCutProfiles.Batch251.profile10066,MergedCutProfiles.Batch251.profile10067,MergedCutProfiles.Batch251.profile10068,MergedCutProfiles.Batch251.profile10069,MergedCutProfiles.Batch251.profile10070,MergedCutProfiles.Batch251.profile10071,MergedCutProfiles.Batch251.profile10072,MergedCutProfiles.Batch251.profile10073,MergedCutProfiles.Batch251.profile10074]⟩
theorem profilesValid1559 : retention1559.ProfilesValid := by
  change ∀ j : Fin 16, (retention1559.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch251.valid10059
  · exact MergedCutProfiles.Batch251.valid10060
  · exact MergedCutProfiles.Batch251.valid10061
  · exact MergedCutProfiles.Batch251.valid10062
  · exact MergedCutProfiles.Batch251.valid10063
  · exact MergedCutProfiles.Batch251.valid10064
  · exact MergedCutProfiles.Batch251.valid10065
  · exact MergedCutProfiles.Batch251.valid10066
  · exact MergedCutProfiles.Batch251.valid10067
  · exact MergedCutProfiles.Batch251.valid10068
  · exact MergedCutProfiles.Batch251.valid10069
  · exact MergedCutProfiles.Batch251.valid10070
  · exact MergedCutProfiles.Batch251.valid10071
  · exact MergedCutProfiles.Batch251.valid10072
  · exact MergedCutProfiles.Batch251.valid10073
  · exact MergedCutProfiles.Batch251.valid10074
theorem numericValid1559 : retention1559.NumericValid := by decide +kernel
def certificate1559 : RatCutBinCertificate := ⟨⟨retention1559,(235080847894458661/100000000000000000),(205886892695735953/1000000000000000000),(4192221140517765803/250000000000000000),(185698677009292092909/1000000000000000000),(1043649858774781107/1000000000000000000)⟩,(197981462140580407/200000000000000000),(426628174155126193/1000000000000000000),(209951254056170013/1000000000000000000),(30901868815604681/200000000000000000)⟩
theorem valid1559 : certificate1559.Valid := by decide +kernel
theorem sound1559 : certificate1559.Sound := rat_cut_bin_certificate_sound certificate1559 profilesValid1559 numericValid1559 valid1559

def certificates : List RatCutBinCertificate := [certificate1548,certificate1549,certificate1550,certificate1551,certificate1552,certificate1553,certificate1554,certificate1555,certificate1556,certificate1557,certificate1558,certificate1559]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound1548,List.forall_mem_cons.mpr ⟨sound1549,List.forall_mem_cons.mpr ⟨sound1550,List.forall_mem_cons.mpr ⟨sound1551,List.forall_mem_cons.mpr ⟨sound1552,List.forall_mem_cons.mpr ⟨sound1553,List.forall_mem_cons.mpr ⟨sound1554,List.forall_mem_cons.mpr ⟨sound1555,List.forall_mem_cons.mpr ⟨sound1556,List.forall_mem_cons.mpr ⟨sound1557,List.forall_mem_cons.mpr ⟨sound1558,List.forall_mem_cons.mpr ⟨sound1559,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch129
