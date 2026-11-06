import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch051
import Cycle12.MergedCutProfiles.Batch052
import Cycle12.MergedCutProfiles.Batch053

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch026

def retention312 : RatCutRetentionCertificate := ⟨(13/400),(33/1000),(746703315665460376/48032495018026366395),(184827553382539697/250000000000000000),(7/2),(4422815755755056543/2000000000000000000),true,MergedCutProfiles.Batch051.profile2047,![MergedCutProfiles.Batch051.profile2047,MergedCutProfiles.Batch051.profile2048,MergedCutProfiles.Batch051.profile2049,MergedCutProfiles.Batch051.profile2050,MergedCutProfiles.Batch051.profile2051,MergedCutProfiles.Batch051.profile2052,MergedCutProfiles.Batch051.profile2053,MergedCutProfiles.Batch051.profile2054,MergedCutProfiles.Batch051.profile2055,MergedCutProfiles.Batch051.profile2056,MergedCutProfiles.Batch051.profile2057,MergedCutProfiles.Batch051.profile2058,MergedCutProfiles.Batch051.profile2059,MergedCutProfiles.Batch051.profile2060,MergedCutProfiles.Batch051.profile2061,MergedCutProfiles.Batch051.profile2062]⟩
theorem profilesValid312 : retention312.ProfilesValid := by
  change ∀ j : Fin 16, (retention312.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch051.valid2047
  · exact MergedCutProfiles.Batch051.valid2048
  · exact MergedCutProfiles.Batch051.valid2049
  · exact MergedCutProfiles.Batch051.valid2050
  · exact MergedCutProfiles.Batch051.valid2051
  · exact MergedCutProfiles.Batch051.valid2052
  · exact MergedCutProfiles.Batch051.valid2053
  · exact MergedCutProfiles.Batch051.valid2054
  · exact MergedCutProfiles.Batch051.valid2055
  · exact MergedCutProfiles.Batch051.valid2056
  · exact MergedCutProfiles.Batch051.valid2057
  · exact MergedCutProfiles.Batch051.valid2058
  · exact MergedCutProfiles.Batch051.valid2059
  · exact MergedCutProfiles.Batch051.valid2060
  · exact MergedCutProfiles.Batch051.valid2061
  · exact MergedCutProfiles.Batch051.valid2062
theorem numericValid312 : retention312.NumericValid := by decide +kernel
def certificate312 : RatCutBinCertificate := ⟨⟨retention312,(1006763177067177437/500000000000000000),(481579510880593/10000000000000000),(10153170022488898843/1000000000000000000),(97787639010132507129/200000000000000000),(1088990021973218629/500000000000000000)⟩,(498036516298394853/500000000000000000),(432115178272633103/1000000000000000000),(205312420010623817/1000000000000000000),(12815014671355473/125000000000000000)⟩
theorem valid312 : certificate312.Valid := by decide +kernel
theorem sound312 : certificate312.Sound := rat_cut_bin_certificate_sound certificate312 profilesValid312 numericValid312 valid312

def retention313 : RatCutRetentionCertificate := ⟨(13/400),(33/1000),(875568362043038242/48032495018026366395),(93337914458182547/125000000000000000),(7/2),(70478046342954655941/32000000000000000000),true,MergedCutProfiles.Batch051.profile2063,![MergedCutProfiles.Batch051.profile2063,MergedCutProfiles.Batch051.profile2064,MergedCutProfiles.Batch051.profile2065,MergedCutProfiles.Batch051.profile2066,MergedCutProfiles.Batch051.profile2067,MergedCutProfiles.Batch051.profile2068,MergedCutProfiles.Batch051.profile2069,MergedCutProfiles.Batch051.profile2070,MergedCutProfiles.Batch051.profile2071,MergedCutProfiles.Batch051.profile2072,MergedCutProfiles.Batch051.profile2073,MergedCutProfiles.Batch051.profile2074,MergedCutProfiles.Batch051.profile2075,MergedCutProfiles.Batch051.profile2076,MergedCutProfiles.Batch051.profile2077,MergedCutProfiles.Batch051.profile2078]⟩
theorem profilesValid313 : retention313.ProfilesValid := by
  change ∀ j : Fin 16, (retention313.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch051.valid2063
  · exact MergedCutProfiles.Batch051.valid2064
  · exact MergedCutProfiles.Batch051.valid2065
  · exact MergedCutProfiles.Batch051.valid2066
  · exact MergedCutProfiles.Batch051.valid2067
  · exact MergedCutProfiles.Batch051.valid2068
  · exact MergedCutProfiles.Batch051.valid2069
  · exact MergedCutProfiles.Batch051.valid2070
  · exact MergedCutProfiles.Batch051.valid2071
  · exact MergedCutProfiles.Batch051.valid2072
  · exact MergedCutProfiles.Batch051.valid2073
  · exact MergedCutProfiles.Batch051.valid2074
  · exact MergedCutProfiles.Batch051.valid2075
  · exact MergedCutProfiles.Batch051.valid2076
  · exact MergedCutProfiles.Batch051.valid2077
  · exact MergedCutProfiles.Batch051.valid2078
theorem numericValid313 : retention313.NumericValid := by decide +kernel
def certificate313 : RatCutBinCertificate := ⟨⟨retention313,(1006763177067177437/500000000000000000),(481579510880593/10000000000000000),(10153170022488898843/1000000000000000000),(97787639010132507129/200000000000000000),(2169011126883894279/1000000000000000000)⟩,(498036516298394853/500000000000000000),(107931581716471813/250000000000000000),(20563885972386723/100000000000000000),(102538633770824093/1000000000000000000)⟩
theorem valid313 : certificate313.Valid := by decide +kernel
theorem sound313 : certificate313.Sound := rat_cut_bin_certificate_sound certificate313 profilesValid313 numericValid313 valid313

def retention314 : RatCutRetentionCertificate := ⟨(13/400),(33/1000),(198746739400000000/9606499003605273279),(437784181021519121/500000000000000000),(61/20),(1396464164975192799617/640000000000000000000),true,MergedCutProfiles.Batch051.profile2079,![MergedCutProfiles.Batch051.profile2079,MergedCutProfiles.Batch052.profile2080,MergedCutProfiles.Batch051.profile2050,MergedCutProfiles.Batch052.profile2081,MergedCutProfiles.Batch052.profile2082,MergedCutProfiles.Batch051.profile2054,MergedCutProfiles.Batch052.profile2083,MergedCutProfiles.Batch052.profile2084,MergedCutProfiles.Batch052.profile2085,MergedCutProfiles.Batch052.profile2086,MergedCutProfiles.Batch052.profile2087,MergedCutProfiles.Batch051.profile2062,MergedCutProfiles.Batch052.profile2088,MergedCutProfiles.Batch052.profile2089,MergedCutProfiles.Batch052.profile2090,MergedCutProfiles.Batch052.profile2091]⟩
theorem profilesValid314 : retention314.ProfilesValid := by
  change ∀ j : Fin 16, (retention314.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch051.valid2079
  · exact MergedCutProfiles.Batch052.valid2080
  · exact MergedCutProfiles.Batch051.valid2050
  · exact MergedCutProfiles.Batch052.valid2081
  · exact MergedCutProfiles.Batch052.valid2082
  · exact MergedCutProfiles.Batch051.valid2054
  · exact MergedCutProfiles.Batch052.valid2083
  · exact MergedCutProfiles.Batch052.valid2084
  · exact MergedCutProfiles.Batch052.valid2085
  · exact MergedCutProfiles.Batch052.valid2086
  · exact MergedCutProfiles.Batch052.valid2087
  · exact MergedCutProfiles.Batch051.valid2062
  · exact MergedCutProfiles.Batch052.valid2088
  · exact MergedCutProfiles.Batch052.valid2089
  · exact MergedCutProfiles.Batch052.valid2090
  · exact MergedCutProfiles.Batch052.valid2091
theorem numericValid314 : retention314.NumericValid := by decide +kernel
def certificate314 : RatCutBinCertificate := ⟨⟨retention314,(1006763177067177437/500000000000000000),(481579510880593/10000000000000000),(10153170022488898843/1000000000000000000),(97787639010132507129/200000000000000000),(1076422661312005947/500000000000000000)⟩,(498036516298394853/500000000000000000),(402706657964574927/1000000000000000000),(231011520398327983/1000000000000000000),(128382419113275841/1000000000000000000)⟩
theorem valid314 : certificate314.Valid := by decide +kernel
theorem sound314 : certificate314.Sound := rat_cut_bin_certificate_sound certificate314 profilesValid314 numericValid314 valid314

def retention315 : RatCutRetentionCertificate := ⟨(13/400),(33/1000),(338835895545375598/16010831672675455465),(993733697/1000000000),(27/10),(4327777354324784559/2000000000000000000),true,MergedCutProfiles.Batch052.profile2092,![MergedCutProfiles.Batch052.profile2092,MergedCutProfiles.Batch052.profile2093,MergedCutProfiles.Batch052.profile2094,MergedCutProfiles.Batch052.profile2095,MergedCutProfiles.Batch052.profile2096,MergedCutProfiles.Batch051.profile2069,MergedCutProfiles.Batch052.profile2097,MergedCutProfiles.Batch052.profile2098,MergedCutProfiles.Batch052.profile2099,MergedCutProfiles.Batch052.profile2100,MergedCutProfiles.Batch051.profile2061,MergedCutProfiles.Batch051.profile2076,MergedCutProfiles.Batch052.profile2101,MergedCutProfiles.Batch052.profile2102,MergedCutProfiles.Batch052.profile2103,MergedCutProfiles.Batch052.profile2104]⟩
theorem profilesValid315 : retention315.ProfilesValid := by
  change ∀ j : Fin 16, (retention315.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch052.valid2092
  · exact MergedCutProfiles.Batch052.valid2093
  · exact MergedCutProfiles.Batch052.valid2094
  · exact MergedCutProfiles.Batch052.valid2095
  · exact MergedCutProfiles.Batch052.valid2096
  · exact MergedCutProfiles.Batch051.valid2069
  · exact MergedCutProfiles.Batch052.valid2097
  · exact MergedCutProfiles.Batch052.valid2098
  · exact MergedCutProfiles.Batch052.valid2099
  · exact MergedCutProfiles.Batch052.valid2100
  · exact MergedCutProfiles.Batch051.valid2061
  · exact MergedCutProfiles.Batch051.valid2076
  · exact MergedCutProfiles.Batch052.valid2101
  · exact MergedCutProfiles.Batch052.valid2102
  · exact MergedCutProfiles.Batch052.valid2103
  · exact MergedCutProfiles.Batch052.valid2104
theorem numericValid315 : retention315.NumericValid := by decide +kernel
def certificate315 : RatCutBinCertificate := ⟨⟨retention315,(1006763177067177437/500000000000000000),(481579510880593/10000000000000000),(10153170022488898843/1000000000000000000),(97787639010132507129/200000000000000000),(427620305184297417/200000000000000000)⟩,(498036516298394853/500000000000000000),(23943840079027853/62500000000000000),(249327557959671113/1000000000000000000),(151753895013909293/1000000000000000000)⟩
theorem valid315 : certificate315.Valid := by decide +kernel
theorem sound315 : certificate315.Sound := rat_cut_bin_certificate_sound certificate315 profilesValid315 numericValid315 valid315

def retention316 : RatCutRetentionCertificate := ⟨(13/400),(33/1000),(1329804380331635773/48032495018026366395),(508253843318063397/500000000000000000),(53/20),(1366732669275660024797/640000000000000000000),true,MergedCutProfiles.Batch052.profile2105,![MergedCutProfiles.Batch052.profile2105,MergedCutProfiles.Batch052.profile2106,MergedCutProfiles.Batch052.profile2081,MergedCutProfiles.Batch052.profile2107,MergedCutProfiles.Batch052.profile2108,MergedCutProfiles.Batch052.profile2084,MergedCutProfiles.Batch052.profile2109,MergedCutProfiles.Batch052.profile2110,MergedCutProfiles.Batch051.profile2062,MergedCutProfiles.Batch052.profile2111,MergedCutProfiles.Batch052.profile2112,MergedCutProfiles.Batch052.profile2113,MergedCutProfiles.Batch052.profile2114,MergedCutProfiles.Batch052.profile2115,MergedCutProfiles.Batch052.profile2116,MergedCutProfiles.Batch052.profile2117]⟩
theorem profilesValid316 : retention316.ProfilesValid := by
  change ∀ j : Fin 16, (retention316.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch052.valid2105
  · exact MergedCutProfiles.Batch052.valid2106
  · exact MergedCutProfiles.Batch052.valid2081
  · exact MergedCutProfiles.Batch052.valid2107
  · exact MergedCutProfiles.Batch052.valid2108
  · exact MergedCutProfiles.Batch052.valid2084
  · exact MergedCutProfiles.Batch052.valid2109
  · exact MergedCutProfiles.Batch052.valid2110
  · exact MergedCutProfiles.Batch051.valid2062
  · exact MergedCutProfiles.Batch052.valid2111
  · exact MergedCutProfiles.Batch052.valid2112
  · exact MergedCutProfiles.Batch052.valid2113
  · exact MergedCutProfiles.Batch052.valid2114
  · exact MergedCutProfiles.Batch052.valid2115
  · exact MergedCutProfiles.Batch052.valid2116
  · exact MergedCutProfiles.Batch052.valid2117
theorem numericValid316 : retention316.NumericValid := by decide +kernel
def certificate316 : RatCutBinCertificate := ⟨⟨retention316,(1006763177067177437/500000000000000000),(481579510880593/10000000000000000),(10153170022488898843/1000000000000000000),(97787639010132507129/200000000000000000),(2110210188018255911/1000000000000000000)⟩,(498036516298394853/500000000000000000),(384400292248225523/1000000000000000000),(124041825851688757/500000000000000000),(75892043240558837/500000000000000000)⟩
theorem valid316 : certificate316.Valid := by decide +kernel
theorem sound316 : certificate316.Sound := rat_cut_bin_certificate_sound certificate316 profilesValid316 numericValid316 valid316

def retention317 : RatCutRetentionCertificate := ⟨(13/400),(33/1000),(5462894787429115676/48032495018026366395),(1329804380331635773/1000000000000000000),(11/5),(2372921495957691889073/1280000000000000000000),true,MergedCutProfiles.Batch052.profile2118,![MergedCutProfiles.Batch052.profile2118,MergedCutProfiles.Batch052.profile2087,MergedCutProfiles.Batch052.profile2119,MergedCutProfiles.Batch053.profile2120,MergedCutProfiles.Batch053.profile2121,MergedCutProfiles.Batch053.profile2122,MergedCutProfiles.Batch053.profile2123,MergedCutProfiles.Batch053.profile2124,MergedCutProfiles.Batch053.profile2125,MergedCutProfiles.Batch053.profile2126,MergedCutProfiles.Batch053.profile2127,MergedCutProfiles.Batch053.profile2128,MergedCutProfiles.Batch053.profile2129,MergedCutProfiles.Batch053.profile2130,MergedCutProfiles.Batch053.profile2131,MergedCutProfiles.Batch053.profile2132]⟩
theorem profilesValid317 : retention317.ProfilesValid := by
  change ∀ j : Fin 16, (retention317.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch052.valid2118
  · exact MergedCutProfiles.Batch052.valid2087
  · exact MergedCutProfiles.Batch052.valid2119
  · exact MergedCutProfiles.Batch053.valid2120
  · exact MergedCutProfiles.Batch053.valid2121
  · exact MergedCutProfiles.Batch053.valid2122
  · exact MergedCutProfiles.Batch053.valid2123
  · exact MergedCutProfiles.Batch053.valid2124
  · exact MergedCutProfiles.Batch053.valid2125
  · exact MergedCutProfiles.Batch053.valid2126
  · exact MergedCutProfiles.Batch053.valid2127
  · exact MergedCutProfiles.Batch053.valid2128
  · exact MergedCutProfiles.Batch053.valid2129
  · exact MergedCutProfiles.Batch053.valid2130
  · exact MergedCutProfiles.Batch053.valid2131
  · exact MergedCutProfiles.Batch053.valid2132
theorem numericValid317 : retention317.NumericValid := by decide +kernel
def certificate317 : RatCutBinCertificate := ⟨⟨retention317,(1006763177067177437/500000000000000000),(481579510880593/10000000000000000),(10153170022488898843/1000000000000000000),(97787639010132507129/200000000000000000),(229104153723051311/125000000000000000)⟩,(498036516298394853/500000000000000000),(398015624272479413/1000000000000000000),(235305475353390053/1000000000000000000),(151897461380454967/1000000000000000000)⟩
theorem valid317 : certificate317.Valid := by decide +kernel
theorem sound317 : certificate317.Sound := rat_cut_bin_certificate_sound certificate317 profilesValid317 numericValid317 valid317

def retention318 : RatCutRetentionCertificate := ⟨(13/400),(33/1000),(20316279342605662501/48032495018026366395),(1365723696857278919/250000000000000000),(11/10),(622834025778923581767793118841386782951/546289478742911567600000000000000000000),false,MergedCutProfiles.Batch053.profile2133,(fun _ => MergedCutProfiles.Batch053.profile2133)⟩
theorem profilesValid318 : retention318.ProfilesValid := by
  exact MergedCutProfiles.Batch053.valid2133
theorem numericValid318 : retention318.NumericValid := by decide +kernel
def certificate318 : RatCutBinCertificate := ⟨⟨retention318,(1006763177067177437/500000000000000000),(481579510880593/10000000000000000),(10153170022488898843/1000000000000000000),(97787639010132507129/200000000000000000),(1129611527665677949/1000000000000000000)⟩,(498036516298394853/500000000000000000),(468319471069697913/1000000000000000000),(17641107883284043/100000000000000000),(77032493735358049/500000000000000000)⟩
theorem valid318 : certificate318.Valid := by decide +kernel
theorem sound318 : certificate318.Sound := rat_cut_bin_certificate_sound certificate318 profilesValid318 numericValid318 valid318

def retention319 : RatCutRetentionCertificate := ⟨(13/400),(33/1000),(23822435301443876344/48032495018026366395),(20316279342605662501/1000000000000000000),1,(506399649927499235281498357420194693/507906983565141562525000000000000000),false,MergedCutProfiles.Batch053.profile2134,(fun _ => MergedCutProfiles.Batch053.profile2134)⟩
theorem profilesValid319 : retention319.ProfilesValid := by
  exact MergedCutProfiles.Batch053.valid2134
theorem numericValid319 : retention319.NumericValid := by decide +kernel
def certificate319 : RatCutBinCertificate := ⟨⟨retention319,(1006763177067177437/500000000000000000),(481579510880593/10000000000000000),(10153170022488898843/1000000000000000000),(97787639010132507129/200000000000000000),(987481771934295707/1000000000000000000)⟩,(498036516298394853/500000000000000000),(48796918202088173/100000000000000000),(80955687738467423/500000000000000000),(75929696587331337/500000000000000000)⟩
theorem valid319 : certificate319.Valid := by decide +kernel
theorem sound319 : certificate319.Sound := rat_cut_bin_certificate_sound certificate319 profilesValid319 numericValid319 valid319

def retention320 : RatCutRetentionCertificate := ⟨(13/400),(33/1000),(1/2),(2977804412680484543/125000000000000000),1,(18885729979874870833378055098196917091/19057948241155101075200000000000000000),false,MergedCutProfiles.Batch053.profile2135,(fun _ => MergedCutProfiles.Batch053.profile2135)⟩
theorem profilesValid320 : retention320.ProfilesValid := by
  exact MergedCutProfiles.Batch053.valid2135
theorem numericValid320 : retention320.NumericValid := by decide +kernel
def certificate320 : RatCutBinCertificate := ⟨⟨retention320,(1006763177067177437/500000000000000000),(481579510880593/10000000000000000),(10153170022488898843/1000000000000000000),(97787639010132507129/200000000000000000),(49070647800129143/50000000000000000)⟩,(498036516298394853/500000000000000000),(244192803421200723/500000000000000000),(32322553631674209/200000000000000000),(75860911795938729/500000000000000000)⟩
theorem valid320 : certificate320.Valid := by decide +kernel
theorem sound320 : certificate320.Sound := rat_cut_bin_certificate_sound certificate320 profilesValid320 numericValid320 valid320

def retention321 : RatCutRetentionCertificate := ⟨(13/400),(33/1000),(6757361290720103408/16010831672675455465),(924450126468980281/250000000000000000),(5/4),(1068067681202659566345418748929279861/924450126468980281000000000000000000),false,MergedCutProfiles.Batch053.profile2136,(fun _ => MergedCutProfiles.Batch053.profile2136)⟩
theorem profilesValid321 : retention321.ProfilesValid := by
  exact MergedCutProfiles.Batch053.valid2136
theorem numericValid321 : retention321.NumericValid := by decide +kernel
def certificate321 : RatCutBinCertificate := ⟨⟨retention321,(1199906440567177437/500000000000000000),(481579510880593/10000000000000000),(10153170022488898843/1000000000000000000),(97787639010132507129/200000000000000000),(285281486559892331/250000000000000000)⟩,(62207468005997529/62500000000000000),(44484439184908599/125000000000000000),(276438137857072301/1000000000000000000),(209671353213982793/1000000000000000000)⟩
theorem valid321 : certificate321.Valid := by decide +kernel
theorem sound321 : certificate321.Sound := rat_cut_bin_certificate_sound certificate321 profilesValid321 numericValid321 valid321

def retention322 : RatCutRetentionCertificate := ⟨(13/400),(33/1000),(23770612636597299802/48032495018026366395),(1267005242010019389/62500000000000000),1,(4050824840221909388129580019764788563/4054416774432062044800000000000000000),false,MergedCutProfiles.Batch053.profile2137,(fun _ => MergedCutProfiles.Batch053.profile2137)⟩
theorem profilesValid322 : retention322.ProfilesValid := by
  exact MergedCutProfiles.Batch053.valid2137
theorem numericValid322 : retention322.NumericValid := by decide +kernel
def certificate322 : RatCutBinCertificate := ⟨⟨retention322,(1199906440567177437/500000000000000000),(481579510880593/10000000000000000),(10153170022488898843/1000000000000000000),(97787639010132507129/200000000000000000),(987731354599609073/1000000000000000000)⟩,(62207468005997529/62500000000000000),(205571474557037381/500000000000000000),(223426354952242397/1000000000000000000),(104713017468864387/500000000000000000)⟩
theorem valid322 : certificate322.Valid := by decide +kernel
theorem sound322 : certificate322.Sound := rat_cut_bin_certificate_sound certificate322 profilesValid322 numericValid322 valid322

def retention323 : RatCutRetentionCertificate := ⟨(13/400),(33/1000),(24008318762963272801/48032495018026366395),(11885306318298649901/500000000000000000),1,(18850365217057650978883122219569083683/19016490109277839841600000000000000000),false,MergedCutProfiles.Batch053.profile2138,(fun _ => MergedCutProfiles.Batch053.profile2138)⟩
theorem profilesValid323 : retention323.ProfilesValid := by
  exact MergedCutProfiles.Batch053.valid2138
theorem numericValid323 : retention323.NumericValid := by decide +kernel
def certificate323 : RatCutBinCertificate := ⟨⟨retention323,(1199906440567177437/500000000000000000),(481579510880593/10000000000000000),(10153170022488898843/1000000000000000000),(97787639010132507129/200000000000000000),(489940730183378931/500000000000000000)⟩,(62207468005997529/62500000000000000),(414436642071506599/1000000000000000000),(27564015480487121/125000000000000000),(103265973434005269/500000000000000000)⟩
theorem valid323 : certificate323.Valid := by decide +kernel
theorem sound323 : certificate323.Sound := rat_cut_bin_certificate_sound certificate323 profilesValid323 numericValid323 valid323

def certificates : List RatCutBinCertificate := [certificate312,certificate313,certificate314,certificate315,certificate316,certificate317,certificate318,certificate319,certificate320,certificate321,certificate322,certificate323]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound312,List.forall_mem_cons.mpr ⟨sound313,List.forall_mem_cons.mpr ⟨sound314,List.forall_mem_cons.mpr ⟨sound315,List.forall_mem_cons.mpr ⟨sound316,List.forall_mem_cons.mpr ⟨sound317,List.forall_mem_cons.mpr ⟨sound318,List.forall_mem_cons.mpr ⟨sound319,List.forall_mem_cons.mpr ⟨sound320,List.forall_mem_cons.mpr ⟨sound321,List.forall_mem_cons.mpr ⟨sound322,List.forall_mem_cons.mpr ⟨sound323,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch026
