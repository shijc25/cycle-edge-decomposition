import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch003
import Cycle12.MergedCutProfiles.Batch004
import Cycle12.MergedCutProfiles.Batch005
import Cycle12.MergedCutProfiles.Batch307
import Cycle12.MergedCutProfiles.Batch308

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch162

def retention1944 : RatCutRetentionCertificate := ⟨(1/250),(1/200),(195055227938534645/1593365752697607446664),(286817804046467961/500000000000000000),4,(9886933233005578324835187167390959/4481528188226061890625000000000000),true,MergedCutProfiles.Batch307.profile12314,![MergedCutProfiles.Batch307.profile12314,MergedCutProfiles.Batch003.profile126,MergedCutProfiles.Batch307.profile12315,MergedCutProfiles.Batch003.profile127,MergedCutProfiles.Batch003.profile142,MergedCutProfiles.Batch307.profile12316,MergedCutProfiles.Batch003.profile128,MergedCutProfiles.Batch003.profile129,MergedCutProfiles.Batch003.profile129,MergedCutProfiles.Batch307.profile12317,MergedCutProfiles.Batch003.profile130,MergedCutProfiles.Batch307.profile12318,MergedCutProfiles.Batch003.profile131,MergedCutProfiles.Batch003.profile132,MergedCutProfiles.Batch003.profile132,MergedCutProfiles.Batch307.profile12319]⟩
theorem profilesValid1944 : retention1944.ProfilesValid := by
  change ∀ j : Fin 16, (retention1944.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch307.valid12314
  · exact MergedCutProfiles.Batch003.valid126
  · exact MergedCutProfiles.Batch307.valid12315
  · exact MergedCutProfiles.Batch003.valid127
  · exact MergedCutProfiles.Batch003.valid142
  · exact MergedCutProfiles.Batch307.valid12316
  · exact MergedCutProfiles.Batch003.valid128
  · exact MergedCutProfiles.Batch003.valid129
  · exact MergedCutProfiles.Batch003.valid129
  · exact MergedCutProfiles.Batch307.valid12317
  · exact MergedCutProfiles.Batch003.valid130
  · exact MergedCutProfiles.Batch307.valid12318
  · exact MergedCutProfiles.Batch003.valid131
  · exact MergedCutProfiles.Batch003.valid132
  · exact MergedCutProfiles.Batch003.valid132
  · exact MergedCutProfiles.Batch307.valid12319
theorem numericValid1944 : retention1944.NumericValid := by decide +kernel
def certificate1944 : RatCutBinCertificate := ⟨⟨retention1944,(900264851882168687/500000000000000000),(249776479000013/250000000000000000),(3499827725437264927/500000000000000000),(3360552228563666647927/100000000000000000),(2205124186510095279/1000000000000000000)⟩,(999946455763114051/1000000000000000000),(577998514748479187/1000000000000000000),(105151956512749467/1000000000000000000),(46735915457848337/1000000000000000000)⟩
theorem valid1944 : certificate1944.Valid := by decide +kernel
theorem sound1944 : certificate1944.Sound := rat_cut_bin_certificate_sound certificate1944 profilesValid1944 numericValid1944 valid1944

def retention1945 : RatCutRetentionCertificate := ⟨(1/250),(1/200),(3254319500000000/11715924652188290049),(117033136763120787/200000000000000000),4,(1737512343077650146252870183569061333/780220911754138580000000000000000000),true,MergedCutProfiles.Batch003.profile126,![MergedCutProfiles.Batch003.profile126,MergedCutProfiles.Batch003.profile142,MergedCutProfiles.Batch003.profile128,MergedCutProfiles.Batch307.profile12317,MergedCutProfiles.Batch307.profile12318,MergedCutProfiles.Batch003.profile131,MergedCutProfiles.Batch307.profile12319,MergedCutProfiles.Batch003.profile134,MergedCutProfiles.Batch308.profile12320,MergedCutProfiles.Batch003.profile135,MergedCutProfiles.Batch003.profile137,MergedCutProfiles.Batch003.profile138,MergedCutProfiles.Batch003.profile151,MergedCutProfiles.Batch003.profile139,MergedCutProfiles.Batch003.profile141,MergedCutProfiles.Batch308.profile12321]⟩
theorem profilesValid1945 : retention1945.ProfilesValid := by
  change ∀ j : Fin 16, (retention1945.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch003.valid126
  · exact MergedCutProfiles.Batch003.valid142
  · exact MergedCutProfiles.Batch003.valid128
  · exact MergedCutProfiles.Batch307.valid12317
  · exact MergedCutProfiles.Batch307.valid12318
  · exact MergedCutProfiles.Batch003.valid131
  · exact MergedCutProfiles.Batch307.valid12319
  · exact MergedCutProfiles.Batch003.valid134
  · exact MergedCutProfiles.Batch308.valid12320
  · exact MergedCutProfiles.Batch003.valid135
  · exact MergedCutProfiles.Batch003.valid137
  · exact MergedCutProfiles.Batch003.valid138
  · exact MergedCutProfiles.Batch003.valid151
  · exact MergedCutProfiles.Batch003.valid139
  · exact MergedCutProfiles.Batch003.valid141
  · exact MergedCutProfiles.Batch308.valid12321
theorem numericValid1945 : retention1945.NumericValid := by decide +kernel
def certificate1945 : RatCutBinCertificate := ⟨⟨retention1945,(900264851882168687/500000000000000000),(249776479000013/250000000000000000),(3499827725437264927/500000000000000000),(3360552228563666647927/100000000000000000),(278240150649742897/125000000000000000)⟩,(999946455763114051/1000000000000000000),(282427805075890513/500000000000000000),(28126814008292767/250000000000000000),(25289574127576863/500000000000000000)⟩
theorem valid1945 : certificate1945.Valid := by decide +kernel
theorem sound1945 : certificate1945.Sound := rat_cut_bin_certificate_sound certificate1945 profilesValid1945 numericValid1945 valid1945

def retention1946 : RatCutRetentionCertificate := ⟨(1/250),(1/200),(1777803176127737665/1195024314523205584998),(331940589/250000000),(12/5),(37147930749592986743/16000000000000000000),true,MergedCutProfiles.Batch307.profile12318,![MergedCutProfiles.Batch307.profile12318,MergedCutProfiles.Batch003.profile136,MergedCutProfiles.Batch308.profile12321,MergedCutProfiles.Batch003.profile145,MergedCutProfiles.Batch003.profile148,MergedCutProfiles.Batch003.profile150,MergedCutProfiles.Batch003.profile154,MergedCutProfiles.Batch308.profile12322,MergedCutProfiles.Batch308.profile12323,MergedCutProfiles.Batch308.profile12324,MergedCutProfiles.Batch308.profile12325,MergedCutProfiles.Batch308.profile12326,MergedCutProfiles.Batch308.profile12327,MergedCutProfiles.Batch004.profile160,MergedCutProfiles.Batch004.profile161,MergedCutProfiles.Batch308.profile12328]⟩
theorem profilesValid1946 : retention1946.ProfilesValid := by
  change ∀ j : Fin 16, (retention1946.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch307.valid12318
  · exact MergedCutProfiles.Batch003.valid136
  · exact MergedCutProfiles.Batch308.valid12321
  · exact MergedCutProfiles.Batch003.valid145
  · exact MergedCutProfiles.Batch003.valid148
  · exact MergedCutProfiles.Batch003.valid150
  · exact MergedCutProfiles.Batch003.valid154
  · exact MergedCutProfiles.Batch308.valid12322
  · exact MergedCutProfiles.Batch308.valid12323
  · exact MergedCutProfiles.Batch308.valid12324
  · exact MergedCutProfiles.Batch308.valid12325
  · exact MergedCutProfiles.Batch308.valid12326
  · exact MergedCutProfiles.Batch308.valid12327
  · exact MergedCutProfiles.Batch004.valid160
  · exact MergedCutProfiles.Batch004.valid161
  · exact MergedCutProfiles.Batch308.valid12328
theorem numericValid1946 : retention1946.NumericValid := by decide +kernel
def certificate1946 : RatCutBinCertificate := ⟨⟨retention1946,(900264851882168687/500000000000000000),(249776479000013/250000000000000000),(3499827725437264927/500000000000000000),(3360552228563666647927/100000000000000000),(2321128868954033963/1000000000000000000)⟩,(999946455763114051/1000000000000000000),(335084654418084833/1000000000000000000),(11941372190456757/40000000000000000),(110742770638340057/500000000000000000)⟩
theorem valid1946 : certificate1946.Valid := by decide +kernel
theorem sound1946 : certificate1946.Sound := rat_cut_bin_certificate_sound certificate1946 profilesValid1946 numericValid1946 valid1946

def retention1947 : RatCutRetentionCertificate := ⟨(1/250),(1/200),(8000000000000000000/597512157261602792499),(355560635225547533/50000000000000000),(11/10),(61545005405386600444854154302353736391/28444850818043802640000000000000000000),true,MergedCutProfiles.Batch308.profile12323,![MergedCutProfiles.Batch308.profile12323,MergedCutProfiles.Batch004.profile165,MergedCutProfiles.Batch308.profile12329,MergedCutProfiles.Batch004.profile166,MergedCutProfiles.Batch308.profile12330,MergedCutProfiles.Batch004.profile167,MergedCutProfiles.Batch308.profile12331,MergedCutProfiles.Batch004.profile168,MergedCutProfiles.Batch308.profile12332,MergedCutProfiles.Batch004.profile169,MergedCutProfiles.Batch308.profile12333,MergedCutProfiles.Batch004.profile170,MergedCutProfiles.Batch308.profile12334,MergedCutProfiles.Batch004.profile171,MergedCutProfiles.Batch308.profile12335,MergedCutProfiles.Batch004.profile172]⟩
theorem profilesValid1947 : retention1947.ProfilesValid := by
  change ∀ j : Fin 16, (retention1947.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch308.valid12323
  · exact MergedCutProfiles.Batch004.valid165
  · exact MergedCutProfiles.Batch308.valid12329
  · exact MergedCutProfiles.Batch004.valid166
  · exact MergedCutProfiles.Batch308.valid12330
  · exact MergedCutProfiles.Batch004.valid167
  · exact MergedCutProfiles.Batch308.valid12331
  · exact MergedCutProfiles.Batch004.valid168
  · exact MergedCutProfiles.Batch308.valid12332
  · exact MergedCutProfiles.Batch004.valid169
  · exact MergedCutProfiles.Batch308.valid12333
  · exact MergedCutProfiles.Batch004.valid170
  · exact MergedCutProfiles.Batch308.valid12334
  · exact MergedCutProfiles.Batch004.valid171
  · exact MergedCutProfiles.Batch308.valid12335
  · exact MergedCutProfiles.Batch004.valid172
theorem numericValid1947 : retention1947.NumericValid := by decide +kernel
def certificate1947 : RatCutBinCertificate := ⟨⟨retention1947,(900264851882168687/500000000000000000),(249776479000013/250000000000000000),(3499827725437264927/500000000000000000),(3360552228563666647927/100000000000000000),(2163377983663728477/1000000000000000000)⟩,(999946455763114051/1000000000000000000),(27182395100070127/125000000000000000),(56320135094995607/125000000000000000),(141610354926343383/200000000000000000)⟩
theorem valid1947 : certificate1947.Valid := by decide +kernel
theorem sound1947 : certificate1947.Sound := rat_cut_bin_certificate_sound certificate1947 profilesValid1947 numericValid1947 valid1947

def retention1948 : RatCutRetentionCertificate := ⟨(1/250),(1/200),(1/2),64,1,(63842214036820242051452344238848143879/64000000000000000000000000000000000000),false,MergedCutProfiles.Batch004.profile181,(fun _ => MergedCutProfiles.Batch004.profile181)⟩
theorem profilesValid1948 : retention1948.ProfilesValid := by
  exact MergedCutProfiles.Batch004.valid181
theorem numericValid1948 : retention1948.NumericValid := by decide +kernel
def certificate1948 : RatCutBinCertificate := ⟨⟨retention1948,(900264851882168687/500000000000000000),(249776479000013/250000000000000000),(3499827725437264927/500000000000000000),(3360552228563666647927/100000000000000000),(997277593121124769/1000000000000000000)⟩,(999946455763114051/1000000000000000000),(204421391736762981/500000000000000000),(3523080488848073/15625000000000000),(110700595904795463/500000000000000000)⟩
theorem valid1948 : certificate1948.Valid := by decide +kernel
theorem sound1948 : certificate1948.Sound := rat_cut_bin_certificate_sound certificate1948 profilesValid1948 numericValid1948 valid1948

def retention1949 : RatCutRetentionCertificate := ⟨(1/250),(1/200),(8000000000000000000/597512157261602792499),(910224633697091599/200000000000000000),(23/20),(613865117540853721603177265204497378191/291271882783069311680000000000000000000),false,MergedCutProfiles.Batch308.profile12336,(fun _ => MergedCutProfiles.Batch308.profile12336)⟩
theorem profilesValid1949 : retention1949.ProfilesValid := by
  exact MergedCutProfiles.Batch308.valid12336
theorem numericValid1949 : retention1949.NumericValid := by decide +kernel
def certificate1949 : RatCutBinCertificate := ⟨⟨retention1949,(1031435111382168687/500000000000000000),(249776479000013/250000000000000000),(3499827725437264927/500000000000000000),(3360552228563666647927/100000000000000000),(1053597214749220303/500000000000000000)⟩,(999938654268134887/1000000000000000000),(24229106644047979/200000000000000000),(621130570662723687/1000000000000000000),(421469087072930843/500000000000000000)⟩
theorem valid1949 : certificate1949.Valid := by decide +kernel
theorem sound1949 : certificate1949.Sound := rat_cut_bin_certificate_sound certificate1949 profilesValid1949 numericValid1949 valid1949

def retention1950 : RatCutRetentionCertificate := ⟨(1/250),(1/200),(1/2),64,1,(63842214036820242051452344238848143879/64000000000000000000000000000000000000),false,MergedCutProfiles.Batch004.profile181,(fun _ => MergedCutProfiles.Batch004.profile181)⟩
theorem profilesValid1950 : retention1950.ProfilesValid := by
  exact MergedCutProfiles.Batch004.valid181
theorem numericValid1950 : retention1950.NumericValid := by decide +kernel
def certificate1950 : RatCutBinCertificate := ⟨⟨retention1950,(1031435111382168687/500000000000000000),(249776479000013/250000000000000000),(3499827725437264927/500000000000000000),(3360552228563666647927/100000000000000000),(199448029513753711/200000000000000000)⟩,(999938654268134887/1000000000000000000),(255983669914075699/1000000000000000000),(98782371548299677/250000000000000000),(387969343226538933/1000000000000000000)⟩
theorem valid1950 : certificate1950.Valid := by decide +kernel
theorem sound1950 : certificate1950.Sound := rat_cut_bin_certificate_sound certificate1950 profilesValid1950 numericValid1950 valid1950

def retention1951 : RatCutRetentionCertificate := ⟨(1/200),(3/500),(579198396261429096/3304960567845950649313),(573463758674682273/1000000000000000000),4,(5058202072901786648544580682932158143/2293855034698729092000000000000000000),true,MergedCutProfiles.Batch308.profile12337,![MergedCutProfiles.Batch308.profile12337,MergedCutProfiles.Batch004.profile183,MergedCutProfiles.Batch308.profile12338,MergedCutProfiles.Batch004.profile184,MergedCutProfiles.Batch308.profile12339,MergedCutProfiles.Batch308.profile12340,MergedCutProfiles.Batch004.profile185,MergedCutProfiles.Batch004.profile186,MergedCutProfiles.Batch005.profile200,MergedCutProfiles.Batch004.profile187,MergedCutProfiles.Batch308.profile12341,MergedCutProfiles.Batch308.profile12342,MergedCutProfiles.Batch004.profile188,MergedCutProfiles.Batch004.profile189,MergedCutProfiles.Batch308.profile12343,MergedCutProfiles.Batch004.profile190]⟩
theorem profilesValid1951 : retention1951.ProfilesValid := by
  change ∀ j : Fin 16, (retention1951.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch308.valid12337
  · exact MergedCutProfiles.Batch004.valid183
  · exact MergedCutProfiles.Batch308.valid12338
  · exact MergedCutProfiles.Batch004.valid184
  · exact MergedCutProfiles.Batch308.valid12339
  · exact MergedCutProfiles.Batch308.valid12340
  · exact MergedCutProfiles.Batch004.valid185
  · exact MergedCutProfiles.Batch004.valid186
  · exact MergedCutProfiles.Batch005.valid200
  · exact MergedCutProfiles.Batch004.valid187
  · exact MergedCutProfiles.Batch308.valid12341
  · exact MergedCutProfiles.Batch308.valid12342
  · exact MergedCutProfiles.Batch004.valid188
  · exact MergedCutProfiles.Batch004.valid189
  · exact MergedCutProfiles.Batch308.valid12343
  · exact MergedCutProfiles.Batch004.valid190
theorem numericValid1951 : retention1951.NumericValid := by decide +kernel
def certificate1951 : RatCutBinCertificate := ⟨⟨retention1951,(1805461185470863111/1000000000000000000),(721626522366223/500000000000000000),(7083163750326883547/1000000000000000000),(23512646959416672557299/1000000000000000000),(220363822679063781/100000000000000000)⟩,(999923289900961431/1000000000000000000),(580595468044916909/1000000000000000000),(103734173929239707/1000000000000000000),(73722823103161/1600000000000000)⟩
theorem valid1951 : certificate1951.Valid := by decide +kernel
theorem sound1951 : certificate1951.Sound := rat_cut_bin_certificate_sound certificate1951 profilesValid1951 numericValid1951 valid1951

def retention1952 : RatCutRetentionCertificate := ⟨(1/200),(3/500),(1295068034000000000/3304960567845950649313),(72399799532678637/125000000000000000),4,(70845070805155808521/32000000000000000000),true,MergedCutProfiles.Batch308.profile12344,![MergedCutProfiles.Batch308.profile12344,MergedCutProfiles.Batch004.profile199,MergedCutProfiles.Batch004.profile185,MergedCutProfiles.Batch005.profile200,MergedCutProfiles.Batch308.profile12341,MergedCutProfiles.Batch004.profile188,MergedCutProfiles.Batch308.profile12343,MergedCutProfiles.Batch005.profile201,MergedCutProfiles.Batch005.profile212,MergedCutProfiles.Batch004.profile193,MergedCutProfiles.Batch308.profile12345,MergedCutProfiles.Batch004.profile195,MergedCutProfiles.Batch004.profile196,MergedCutProfiles.Batch005.profile202,MergedCutProfiles.Batch004.profile198,MergedCutProfiles.Batch005.profile203]⟩
theorem profilesValid1952 : retention1952.ProfilesValid := by
  change ∀ j : Fin 16, (retention1952.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch308.valid12344
  · exact MergedCutProfiles.Batch004.valid199
  · exact MergedCutProfiles.Batch004.valid185
  · exact MergedCutProfiles.Batch005.valid200
  · exact MergedCutProfiles.Batch308.valid12341
  · exact MergedCutProfiles.Batch004.valid188
  · exact MergedCutProfiles.Batch308.valid12343
  · exact MergedCutProfiles.Batch005.valid201
  · exact MergedCutProfiles.Batch005.valid212
  · exact MergedCutProfiles.Batch004.valid193
  · exact MergedCutProfiles.Batch308.valid12345
  · exact MergedCutProfiles.Batch004.valid195
  · exact MergedCutProfiles.Batch004.valid196
  · exact MergedCutProfiles.Batch005.valid202
  · exact MergedCutProfiles.Batch004.valid198
  · exact MergedCutProfiles.Batch005.valid203
theorem numericValid1952 : retention1952.NumericValid := by decide +kernel
def certificate1952 : RatCutBinCertificate := ⟨⟨retention1952,(1805461185470863111/1000000000000000000),(721626522366223/500000000000000000),(7083163750326883547/1000000000000000000),(23512646959416672557299/1000000000000000000),(138277309511334977/62500000000000000)⟩,(999923289900961431/1000000000000000000),(28718411159769433/50000000000000000),(6697090517567151/62500000000000000),(47840691941143377/1000000000000000000)⟩
theorem valid1952 : certificate1952.Valid := by decide +kernel
theorem sound1952 : certificate1952.Sound := rat_cut_bin_certificate_sound certificate1952 profilesValid1952 numericValid1952 valid1952

def retention1953 : RatCutRetentionCertificate := ⟨(1/200),(3/500),(1296757077754891226/3304960567845950649313),(647534017/500000000),(49/20),(37565941367750950947/16000000000000000000),true,MergedCutProfiles.Batch308.profile12344,![MergedCutProfiles.Batch308.profile12344,MergedCutProfiles.Batch004.profile199,MergedCutProfiles.Batch004.profile185,MergedCutProfiles.Batch005.profile200,MergedCutProfiles.Batch308.profile12341,MergedCutProfiles.Batch004.profile188,MergedCutProfiles.Batch308.profile12343,MergedCutProfiles.Batch005.profile201,MergedCutProfiles.Batch005.profile212,MergedCutProfiles.Batch004.profile193,MergedCutProfiles.Batch308.profile12345,MergedCutProfiles.Batch004.profile195,MergedCutProfiles.Batch004.profile196,MergedCutProfiles.Batch005.profile202,MergedCutProfiles.Batch004.profile198,MergedCutProfiles.Batch005.profile203]⟩
theorem profilesValid1953 : retention1953.ProfilesValid := by
  change ∀ j : Fin 16, (retention1953.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch308.valid12344
  · exact MergedCutProfiles.Batch004.valid199
  · exact MergedCutProfiles.Batch004.valid185
  · exact MergedCutProfiles.Batch005.valid200
  · exact MergedCutProfiles.Batch308.valid12341
  · exact MergedCutProfiles.Batch004.valid188
  · exact MergedCutProfiles.Batch308.valid12343
  · exact MergedCutProfiles.Batch005.valid201
  · exact MergedCutProfiles.Batch005.valid212
  · exact MergedCutProfiles.Batch004.valid193
  · exact MergedCutProfiles.Batch308.valid12345
  · exact MergedCutProfiles.Batch004.valid195
  · exact MergedCutProfiles.Batch004.valid196
  · exact MergedCutProfiles.Batch005.valid202
  · exact MergedCutProfiles.Batch004.valid198
  · exact MergedCutProfiles.Batch005.valid203
theorem numericValid1953 : retention1953.NumericValid := by decide +kernel
def certificate1953 : RatCutBinCertificate := ⟨⟨retention1953,(1805461185470863111/1000000000000000000),(721626522366223/500000000000000000),(7083163750326883547/1000000000000000000),(23512646959416672557299/1000000000000000000),(586742508830506249/250000000000000000)⟩,(999923289900961431/1000000000000000000),(337271825119559879/1000000000000000000),(29615055840428821/100000000000000000),(108944180385725133/500000000000000000)⟩
theorem valid1953 : certificate1953.Valid := by decide +kernel
theorem sound1953 : certificate1953.Sound := rat_cut_bin_certificate_sound certificate1953 profilesValid1953 numericValid1953 valid1953

def retention1954 : RatCutRetentionCertificate := ⟨(1/200),(3/500),(1461218333215000316/3304960567845950649313),(648378538877445613/500000000000000000),(12/5),(302630263999636530332886150523825121991/129675707775489122600000000000000000000),true,MergedCutProfiles.Batch308.profile12344,![MergedCutProfiles.Batch308.profile12344,MergedCutProfiles.Batch308.profile12339,MergedCutProfiles.Batch308.profile12346,MergedCutProfiles.Batch004.profile187,MergedCutProfiles.Batch004.profile188,MergedCutProfiles.Batch308.profile12343,MergedCutProfiles.Batch005.profile201,MergedCutProfiles.Batch005.profile212,MergedCutProfiles.Batch004.profile193,MergedCutProfiles.Batch004.profile194,MergedCutProfiles.Batch004.profile195,MergedCutProfiles.Batch005.profile202,MergedCutProfiles.Batch004.profile197,MergedCutProfiles.Batch005.profile203,MergedCutProfiles.Batch308.profile12347,MergedCutProfiles.Batch308.profile12348]⟩
theorem profilesValid1954 : retention1954.ProfilesValid := by
  change ∀ j : Fin 16, (retention1954.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch308.valid12344
  · exact MergedCutProfiles.Batch308.valid12339
  · exact MergedCutProfiles.Batch308.valid12346
  · exact MergedCutProfiles.Batch004.valid187
  · exact MergedCutProfiles.Batch004.valid188
  · exact MergedCutProfiles.Batch308.valid12343
  · exact MergedCutProfiles.Batch005.valid201
  · exact MergedCutProfiles.Batch005.valid212
  · exact MergedCutProfiles.Batch004.valid193
  · exact MergedCutProfiles.Batch004.valid194
  · exact MergedCutProfiles.Batch004.valid195
  · exact MergedCutProfiles.Batch005.valid202
  · exact MergedCutProfiles.Batch004.valid197
  · exact MergedCutProfiles.Batch005.valid203
  · exact MergedCutProfiles.Batch308.valid12347
  · exact MergedCutProfiles.Batch308.valid12348
theorem numericValid1954 : retention1954.NumericValid := by decide +kernel
def certificate1954 : RatCutBinCertificate := ⟨⟨retention1954,(1805461185470863111/1000000000000000000),(721626522366223/500000000000000000),(7083163750326883547/1000000000000000000),(23512646959416672557299/1000000000000000000),(2332863862415835111/1000000000000000000)⟩,(999923289900961431/1000000000000000000),(67818949307108391/200000000000000000),(58834923435696687/200000000000000000),(217873162620563189/1000000000000000000)⟩
theorem valid1954 : certificate1954.Valid := by decide +kernel
theorem sound1954 : certificate1954.Sound := rat_cut_bin_certificate_sound certificate1954 profilesValid1954 numericValid1954 valid1954

def retention1955 : RatCutRetentionCertificate := ⟨(1/200),(3/500),(64000000000000000000/3304960567845950649313),(365304583303750079/250000000000000000),(9/4),(139824484078837745499/64000000000000000000),true,MergedCutProfiles.Batch308.profile12349,![MergedCutProfiles.Batch308.profile12349,MergedCutProfiles.Batch005.profile220,MergedCutProfiles.Batch308.profile12350,MergedCutProfiles.Batch005.profile221,MergedCutProfiles.Batch308.profile12351,MergedCutProfiles.Batch005.profile222,MergedCutProfiles.Batch308.profile12352,MergedCutProfiles.Batch005.profile223,MergedCutProfiles.Batch308.profile12353,MergedCutProfiles.Batch005.profile224,MergedCutProfiles.Batch308.profile12354,MergedCutProfiles.Batch005.profile225,MergedCutProfiles.Batch308.profile12355,MergedCutProfiles.Batch005.profile226,MergedCutProfiles.Batch308.profile12356,MergedCutProfiles.Batch005.profile227]⟩
theorem profilesValid1955 : retention1955.ProfilesValid := by
  change ∀ j : Fin 16, (retention1955.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch308.valid12349
  · exact MergedCutProfiles.Batch005.valid220
  · exact MergedCutProfiles.Batch308.valid12350
  · exact MergedCutProfiles.Batch005.valid221
  · exact MergedCutProfiles.Batch308.valid12351
  · exact MergedCutProfiles.Batch005.valid222
  · exact MergedCutProfiles.Batch308.valid12352
  · exact MergedCutProfiles.Batch005.valid223
  · exact MergedCutProfiles.Batch308.valid12353
  · exact MergedCutProfiles.Batch005.valid224
  · exact MergedCutProfiles.Batch308.valid12354
  · exact MergedCutProfiles.Batch005.valid225
  · exact MergedCutProfiles.Batch308.valid12355
  · exact MergedCutProfiles.Batch005.valid226
  · exact MergedCutProfiles.Batch308.valid12356
  · exact MergedCutProfiles.Batch005.valid227
theorem numericValid1955 : retention1955.NumericValid := by decide +kernel
def certificate1955 : RatCutBinCertificate := ⟨⟨retention1955,(1805461185470863111/1000000000000000000),(721626522366223/500000000000000000),(7083163750326883547/1000000000000000000),(23512646959416672557299/1000000000000000000),(2183929839093451579/1000000000000000000)⟩,(999923289900961431/1000000000000000000),(342264910980583853/1000000000000000000),(58152321111901067/200000000000000000),(10893792951793509/50000000000000000)⟩
theorem valid1955 : certificate1955.Valid := by decide +kernel
theorem sound1955 : certificate1955.Sound := rat_cut_bin_certificate_sound certificate1955 profilesValid1955 numericValid1955 valid1955

def certificates : List RatCutBinCertificate := [certificate1944,certificate1945,certificate1946,certificate1947,certificate1948,certificate1949,certificate1950,certificate1951,certificate1952,certificate1953,certificate1954,certificate1955]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound1944,List.forall_mem_cons.mpr ⟨sound1945,List.forall_mem_cons.mpr ⟨sound1946,List.forall_mem_cons.mpr ⟨sound1947,List.forall_mem_cons.mpr ⟨sound1948,List.forall_mem_cons.mpr ⟨sound1949,List.forall_mem_cons.mpr ⟨sound1950,List.forall_mem_cons.mpr ⟨sound1951,List.forall_mem_cons.mpr ⟨sound1952,List.forall_mem_cons.mpr ⟨sound1953,List.forall_mem_cons.mpr ⟨sound1954,List.forall_mem_cons.mpr ⟨sound1955,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch162
