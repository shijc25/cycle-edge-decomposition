import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch030
import Cycle12.MergedCutProfiles.Batch031
import Cycle12.MergedCutProfiles.Batch032
import Cycle12.MergedCutProfiles.Batch033
import Cycle12.MergedCutProfiles.Batch324
import Cycle12.MergedCutProfiles.Batch325

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch174

def retention2088 : RatCutRetentionCertificate := ⟨(11/500),(23/1000),(64000000000000000000/207902992142096568441),(5255340545974677743/1000000000000000000),(11/10),(2860629116367303373882892426478958543351/2102136218389871097200000000000000000000),false,MergedCutProfiles.Batch324.profile12982,(fun _ => MergedCutProfiles.Batch324.profile12982)⟩
theorem profilesValid2088 : retention2088.ProfilesValid := by
  exact MergedCutProfiles.Batch324.valid12982
theorem numericValid2088 : retention2088.NumericValid := by decide +kernel
def certificate2088 : RatCutBinCertificate := ⟨⟨retention2088,(2214802841584363907/1000000000000000000),(702642711920787/31250000000000000),(8775682409316870879/1000000000000000000),(1833345959200750119597/1000000000000000000),(1354577928459121393/1000000000000000000)⟩,(199763332896422333/200000000000000000),(177103798526849131/1000000000000000000),(64475756898522203/125000000000000000),(4183804968078039/8000000000000000)⟩
theorem valid2088 : certificate2088.Valid := by decide +kernel
theorem sound2088 : certificate2088.Sound := rat_cut_bin_certificate_sound certificate2088 profilesValid2088 numericValid2088 valid2088

def retention2089 : RatCutRetentionCertificate := ⟨(11/500),(23/1000),(1/2),64,1,(255372377798511361897078253271756735919/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch030.profile1208,(fun _ => MergedCutProfiles.Batch030.profile1208)⟩
theorem profilesValid2089 : retention2089.ProfilesValid := by
  exact MergedCutProfiles.Batch030.valid1208
theorem numericValid2089 : retention2089.NumericValid := by decide +kernel
def certificate2089 : RatCutBinCertificate := ⟨⟨retention2089,(2214802841584363907/1000000000000000000),(702642711920787/31250000000000000),(8775682409316870879/1000000000000000000),(1833345959200750119597/1000000000000000000),(495936852338663323/500000000000000000)⟩,(199763332896422333/200000000000000000),(241866374115427049/1000000000000000000),(207365692258627279/500000000000000000),(404600339805980649/1000000000000000000)⟩
theorem valid2089 : certificate2089.Valid := by decide +kernel
theorem sound2089 : certificate2089.Sound := rat_cut_bin_certificate_sound certificate2089 profilesValid2089 numericValid2089 valid2089

def retention2090 : RatCutRetentionCertificate := ⟨(23/1000),(3/125),(662245790144109025/190011036280601703274),(649196931814634863/1000000000000000000),4,(587864940597472235159/256000000000000000000),true,MergedCutProfiles.Batch324.profile12983,![MergedCutProfiles.Batch324.profile12983,MergedCutProfiles.Batch324.profile12984,MergedCutProfiles.Batch324.profile12985,MergedCutProfiles.Batch324.profile12986,MergedCutProfiles.Batch324.profile12987,MergedCutProfiles.Batch324.profile12988,MergedCutProfiles.Batch324.profile12989,MergedCutProfiles.Batch030.profile1229,MergedCutProfiles.Batch324.profile12990,MergedCutProfiles.Batch031.profile1244,MergedCutProfiles.Batch324.profile12991,MergedCutProfiles.Batch324.profile12992,MergedCutProfiles.Batch324.profile12993,MergedCutProfiles.Batch324.profile12994,MergedCutProfiles.Batch324.profile12995,MergedCutProfiles.Batch030.profile1232]⟩
theorem profilesValid2090 : retention2090.ProfilesValid := by
  change ∀ j : Fin 16, (retention2090.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch324.valid12983
  · exact MergedCutProfiles.Batch324.valid12984
  · exact MergedCutProfiles.Batch324.valid12985
  · exact MergedCutProfiles.Batch324.valid12986
  · exact MergedCutProfiles.Batch324.valid12987
  · exact MergedCutProfiles.Batch324.valid12988
  · exact MergedCutProfiles.Batch324.valid12989
  · exact MergedCutProfiles.Batch030.valid1229
  · exact MergedCutProfiles.Batch324.valid12990
  · exact MergedCutProfiles.Batch031.valid1244
  · exact MergedCutProfiles.Batch324.valid12991
  · exact MergedCutProfiles.Batch324.valid12992
  · exact MergedCutProfiles.Batch324.valid12993
  · exact MergedCutProfiles.Batch324.valid12994
  · exact MergedCutProfiles.Batch324.valid12995
  · exact MergedCutProfiles.Batch030.valid1232
theorem numericValid2090 : retention2090.NumericValid := by decide +kernel
def certificate2090 : RatCutBinCertificate := ⟨⟨retention2090,(239930812649793667/125000000000000000),(12287303118992409/500000000000000000),(8894139533877365657/1000000000000000000),(424558827794382929447/250000000000000000),(1137566749028065111/500000000000000000)⟩,(12486189072394483/12500000000000000),(248894676161571129/500000000000000000),(154963553271040089/1000000000000000000),(72210088698833133/1000000000000000000)⟩
theorem valid2090 : certificate2090.Valid := by decide +kernel
theorem sound2090 : certificate2090.Sound := rat_cut_bin_certificate_sound certificate2090 profilesValid2090 numericValid2090 valid2090

def retention2091 : RatCutRetentionCertificate := ⟨(23/1000),(3/125),(586963955000000000/95005518140300851637),(26489831605764361/40000000000000000),4,(36564683621465526133/16000000000000000000),true,MergedCutProfiles.Batch324.profile12996,![MergedCutProfiles.Batch324.profile12996,MergedCutProfiles.Batch324.profile12997,MergedCutProfiles.Batch030.profile1228,MergedCutProfiles.Batch324.profile12998,MergedCutProfiles.Batch324.profile12999,MergedCutProfiles.Batch030.profile1230,MergedCutProfiles.Batch030.profile1216,MergedCutProfiles.Batch324.profile12994,MergedCutProfiles.Batch030.profile1232,MergedCutProfiles.Batch325.profile13000,MergedCutProfiles.Batch325.profile13001,MergedCutProfiles.Batch030.profile1233,MergedCutProfiles.Batch031.profile1278,MergedCutProfiles.Batch030.profile1222,MergedCutProfiles.Batch030.profile1235,MergedCutProfiles.Batch325.profile13002]⟩
theorem profilesValid2091 : retention2091.ProfilesValid := by
  change ∀ j : Fin 16, (retention2091.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch324.valid12996
  · exact MergedCutProfiles.Batch324.valid12997
  · exact MergedCutProfiles.Batch030.valid1228
  · exact MergedCutProfiles.Batch324.valid12998
  · exact MergedCutProfiles.Batch324.valid12999
  · exact MergedCutProfiles.Batch030.valid1230
  · exact MergedCutProfiles.Batch030.valid1216
  · exact MergedCutProfiles.Batch324.valid12994
  · exact MergedCutProfiles.Batch030.valid1232
  · exact MergedCutProfiles.Batch325.valid13000
  · exact MergedCutProfiles.Batch325.valid13001
  · exact MergedCutProfiles.Batch030.valid1233
  · exact MergedCutProfiles.Batch031.valid1278
  · exact MergedCutProfiles.Batch030.valid1222
  · exact MergedCutProfiles.Batch030.valid1235
  · exact MergedCutProfiles.Batch325.valid13002
theorem numericValid2091 : retention2091.NumericValid := by decide +kernel
def certificate2091 : RatCutBinCertificate := ⟨⟨retention2091,(239930812649793667/125000000000000000),(12287303118992409/500000000000000000),(8894139533877365657/1000000000000000000),(424558827794382929447/250000000000000000),(70752462578691971/31250000000000000)⟩,(12486189072394483/12500000000000000),(98846884544826867/200000000000000000),(157456111566854519/1000000000000000000),(73337688680990789/1000000000000000000)⟩
theorem valid2091 : certificate2091.Valid := by decide +kernel
theorem sound2091 : certificate2091.Sound := rat_cut_bin_certificate_sound certificate2091 profilesValid2091 numericValid2091 valid2091

def retention2092 : RatCutRetentionCertificate := ⟨(23/1000),(3/125),(595593930986519927/95005518140300851637),(117392791/100000000),(5/2),(2653227734775557254712765149163777959/1173927910000000000000000000000000000),true,MergedCutProfiles.Batch324.profile12996,![MergedCutProfiles.Batch324.profile12996,MergedCutProfiles.Batch325.profile13003,MergedCutProfiles.Batch325.profile13004,MergedCutProfiles.Batch325.profile13005,MergedCutProfiles.Batch324.profile12990,MergedCutProfiles.Batch325.profile13006,MergedCutProfiles.Batch325.profile13007,MergedCutProfiles.Batch325.profile13008,MergedCutProfiles.Batch325.profile13009,MergedCutProfiles.Batch325.profile13010,MergedCutProfiles.Batch325.profile13011,MergedCutProfiles.Batch325.profile13012,MergedCutProfiles.Batch031.profile1246,MergedCutProfiles.Batch325.profile13013,MergedCutProfiles.Batch031.profile1259,MergedCutProfiles.Batch030.profile1224]⟩
theorem profilesValid2092 : retention2092.ProfilesValid := by
  change ∀ j : Fin 16, (retention2092.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch324.valid12996
  · exact MergedCutProfiles.Batch325.valid13003
  · exact MergedCutProfiles.Batch325.valid13004
  · exact MergedCutProfiles.Batch325.valid13005
  · exact MergedCutProfiles.Batch324.valid12990
  · exact MergedCutProfiles.Batch325.valid13006
  · exact MergedCutProfiles.Batch325.valid13007
  · exact MergedCutProfiles.Batch325.valid13008
  · exact MergedCutProfiles.Batch325.valid13009
  · exact MergedCutProfiles.Batch325.valid13010
  · exact MergedCutProfiles.Batch325.valid13011
  · exact MergedCutProfiles.Batch325.valid13012
  · exact MergedCutProfiles.Batch031.valid1246
  · exact MergedCutProfiles.Batch325.valid13013
  · exact MergedCutProfiles.Batch031.valid1259
  · exact MergedCutProfiles.Batch030.valid1224
theorem numericValid2092 : retention2092.NumericValid := by decide +kernel
def certificate2092 : RatCutBinCertificate := ⟨⟨retention2092,(239930812649793667/125000000000000000),(12287303118992409/500000000000000000),(8894139533877365657/1000000000000000000),(424558827794382929447/250000000000000000),(1123434820742534257/500000000000000000)⟩,(12486189072394483/12500000000000000),(367230051852359899/1000000000000000000),(264887532819152061/1000000000000000000),(182024216595381321/1000000000000000000)⟩
theorem valid2092 : certificate2092.Valid := by decide +kernel
theorem sound2092 : certificate2092.Sound := rat_cut_bin_certificate_sound certificate2092 profilesValid2092 numericValid2092 valid2092

def retention2093 : RatCutRetentionCertificate := ⟨(23/1000),(3/125),(835366340703961254/95005518140300851637),(595593930986519927/500000000000000000),(5/2),(287660321840207293271/128000000000000000000),true,MergedCutProfiles.Batch325.profile13014,![MergedCutProfiles.Batch325.profile13014,MergedCutProfiles.Batch324.profile12987,MergedCutProfiles.Batch325.profile13015,MergedCutProfiles.Batch031.profile1255,MergedCutProfiles.Batch325.profile13007,MergedCutProfiles.Batch324.profile12995,MergedCutProfiles.Batch325.profile13000,MergedCutProfiles.Batch031.profile1245,MergedCutProfiles.Batch030.profile1221,MergedCutProfiles.Batch325.profile13013,MergedCutProfiles.Batch325.profile13016,MergedCutProfiles.Batch031.profile1247,MergedCutProfiles.Batch325.profile13017,MergedCutProfiles.Batch325.profile13018,MergedCutProfiles.Batch325.profile13019,MergedCutProfiles.Batch031.profile1260]⟩
theorem profilesValid2093 : retention2093.ProfilesValid := by
  change ∀ j : Fin 16, (retention2093.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch325.valid13014
  · exact MergedCutProfiles.Batch324.valid12987
  · exact MergedCutProfiles.Batch325.valid13015
  · exact MergedCutProfiles.Batch031.valid1255
  · exact MergedCutProfiles.Batch325.valid13007
  · exact MergedCutProfiles.Batch324.valid12995
  · exact MergedCutProfiles.Batch325.valid13000
  · exact MergedCutProfiles.Batch031.valid1245
  · exact MergedCutProfiles.Batch030.valid1221
  · exact MergedCutProfiles.Batch325.valid13013
  · exact MergedCutProfiles.Batch325.valid13016
  · exact MergedCutProfiles.Batch031.valid1247
  · exact MergedCutProfiles.Batch325.valid13017
  · exact MergedCutProfiles.Batch325.valid13018
  · exact MergedCutProfiles.Batch325.valid13019
  · exact MergedCutProfiles.Batch031.valid1260
theorem numericValid2093 : retention2093.NumericValid := by decide +kernel
def certificate2093 : RatCutBinCertificate := ⟨⟨retention2093,(239930812649793667/125000000000000000),(12287303118992409/500000000000000000),(8894139533877365657/1000000000000000000),(424558827794382929447/250000000000000000),(1117043784994180643/500000000000000000)⟩,(12486189072394483/12500000000000000),(91716084764744903/250000000000000000),(132627018067453273/500000000000000000),(45524334335690663/250000000000000000)⟩
theorem valid2093 : certificate2093.Valid := by decide +kernel
theorem sound2093 : certificate2093.Sound := rat_cut_bin_certificate_sound certificate2093 profilesValid2093 numericValid2093 valid2093

def retention2094 : RatCutRetentionCertificate := ⟨(23/1000),(3/125),(10151770514292117593/95005518140300851637),(417683170351980627/250000000000000000),2,(65221001763981488046322694470475211/34806930862665052250000000000000000),false,MergedCutProfiles.Batch325.profile13020,(fun _ => MergedCutProfiles.Batch325.profile13020)⟩
theorem profilesValid2094 : retention2094.ProfilesValid := by
  exact MergedCutProfiles.Batch325.valid13020
theorem numericValid2094 : retention2094.NumericValid := by decide +kernel
def certificate2094 : RatCutBinCertificate := ⟨⟨retention2094,(239930812649793667/125000000000000000),(12287303118992409/500000000000000000),(8894139533877365657/1000000000000000000),(424558827794382929447/250000000000000000),(1863186577635888611/1000000000000000000)⟩,(12486189072394483/12500000000000000),(382152531968585531/1000000000000000000),(50047821378128193/200000000000000000),(18206990094668237/100000000000000000)⟩
theorem valid2094 : certificate2094.Valid := by decide +kernel
theorem sound2094 : certificate2094.Sound := rat_cut_bin_certificate_sound certificate2094 profilesValid2094 numericValid2094 valid2094

def retention2095 : RatCutRetentionCertificate := ⟨(23/1000),(3/125),(32000000000000000000/95005518140300851637),(10151770514292117593/500000000000000000),1,(106671881542267797626980506493738405303/81214164114336940744000000000000000000),false,MergedCutProfiles.Batch325.profile13021,(fun _ => MergedCutProfiles.Batch325.profile13021)⟩
theorem profilesValid2095 : retention2095.ProfilesValid := by
  exact MergedCutProfiles.Batch325.valid13021
theorem numericValid2095 : retention2095.NumericValid := by decide +kernel
def certificate2095 : RatCutBinCertificate := ⟨⟨retention2095,(239930812649793667/125000000000000000),(12287303118992409/500000000000000000),(8894139533877365657/1000000000000000000),(424558827794382929447/250000000000000000),(1308160552706948103/1000000000000000000)⟩,(12486189072394483/12500000000000000),(178406982590128893/500000000000000000),(137734960016519919/500000000000000000),(338162787216465673/1000000000000000000)⟩
theorem valid2095 : certificate2095.Valid := by decide +kernel
theorem sound2095 : certificate2095.Sound := rat_cut_bin_certificate_sound certificate2095 profilesValid2095 numericValid2095 valid2095

def retention2096 : RatCutRetentionCertificate := ⟨(23/1000),(3/125),(1/2),64,1,(63843201752088532725087077875070337159/64000000000000000000000000000000000000),false,MergedCutProfiles.Batch032.profile1296,(fun _ => MergedCutProfiles.Batch032.profile1296)⟩
theorem profilesValid2096 : retention2096.ProfilesValid := by
  exact MergedCutProfiles.Batch032.valid1296
theorem numericValid2096 : retention2096.NumericValid := by decide +kernel
def certificate2096 : RatCutBinCertificate := ⟨⟨retention2096,(239930812649793667/125000000000000000),(12287303118992409/500000000000000000),(8894139533877365657/1000000000000000000),(424558827794382929447/250000000000000000),(39689862967707919/40000000000000000)⟩,(12486189072394483/12500000000000000),(455285624322967003/1000000000000000000),(7459264467364857/40000000000000000),(182007760012142507/1000000000000000000)⟩
theorem valid2096 : certificate2096.Valid := by decide +kernel
theorem sound2096 : certificate2096.Sound := rat_cut_bin_certificate_sound certificate2096 profilesValid2096 numericValid2096 valid2096

def retention2097 : RatCutRetentionCertificate := ⟨(23/1000),(3/125),(32000000000000000000/95005518140300851637),(5305075133442116517/1000000000000000000),(11/10),(2769018182940578547436997048426451287951/2122030053376846606800000000000000000000),false,MergedCutProfiles.Batch325.profile13021,(fun _ => MergedCutProfiles.Batch325.profile13021)⟩
theorem profilesValid2097 : retention2097.ProfilesValid := by
  exact MergedCutProfiles.Batch325.valid13021
theorem numericValid2097 : retention2097.NumericValid := by decide +kernel
def certificate2097 : RatCutBinCertificate := ⟨⟨retention2097,(277861944649793667/125000000000000000),(12287303118992409/500000000000000000),(8894139533877365657/1000000000000000000),(424558827794382929447/250000000000000000),(1298135034316339171/1000000000000000000)⟩,(249680112230873521/250000000000000000),(18338676518287857/100000000000000000),(126278536993835001/250000000000000000),(247574638020328407/500000000000000000)⟩
theorem valid2097 : certificate2097.Valid := by decide +kernel
theorem sound2097 : certificate2097.Sound := rat_cut_bin_certificate_sound certificate2097 profilesValid2097 numericValid2097 valid2097

def retention2098 : RatCutRetentionCertificate := ⟨(23/1000),(3/125),(1/2),64,1,(63843201752088532725087077875070337159/64000000000000000000000000000000000000),false,MergedCutProfiles.Batch032.profile1296,(fun _ => MergedCutProfiles.Batch032.profile1296)⟩
theorem profilesValid2098 : retention2098.ProfilesValid := by
  exact MergedCutProfiles.Batch032.valid1296
theorem numericValid2098 : retention2098.NumericValid := by decide +kernel
def certificate2098 : RatCutBinCertificate := ⟨⟨retention2098,(277861944649793667/125000000000000000),(12287303118992409/500000000000000000),(8894139533877365657/1000000000000000000),(424558827794382929447/250000000000000000),(495704070446881347/500000000000000000)⟩,(249680112230873521/250000000000000000),(120061947695539763/500000000000000000),(417206187280193421/1000000000000000000),(203393541556065719/500000000000000000)⟩
theorem valid2098 : certificate2098.Valid := by decide +kernel
theorem sound2098 : certificate2098.Sound := rat_cut_bin_certificate_sound certificate2098 profilesValid2098 numericValid2098 valid2098

def retention2099 : RatCutRetentionCertificate := ⟨(3/125),(1/40),(330441337549969361/87129209707661412453),(654339282277167051/1000000000000000000),4,(36784381757494471263/16000000000000000000),true,MergedCutProfiles.Batch325.profile13022,![MergedCutProfiles.Batch325.profile13022,MergedCutProfiles.Batch325.profile13023,MergedCutProfiles.Batch325.profile13024,MergedCutProfiles.Batch325.profile13025,MergedCutProfiles.Batch325.profile13026,MergedCutProfiles.Batch325.profile13027,MergedCutProfiles.Batch325.profile13028,MergedCutProfiles.Batch032.profile1318,MergedCutProfiles.Batch325.profile13029,MergedCutProfiles.Batch033.profile1332,MergedCutProfiles.Batch325.profile13030,MergedCutProfiles.Batch325.profile13031,MergedCutProfiles.Batch325.profile13032,MergedCutProfiles.Batch325.profile13033,MergedCutProfiles.Batch325.profile13034,MergedCutProfiles.Batch033.profile1320]⟩
theorem profilesValid2099 : retention2099.ProfilesValid := by
  change ∀ j : Fin 16, (retention2099.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch325.valid13022
  · exact MergedCutProfiles.Batch325.valid13023
  · exact MergedCutProfiles.Batch325.valid13024
  · exact MergedCutProfiles.Batch325.valid13025
  · exact MergedCutProfiles.Batch325.valid13026
  · exact MergedCutProfiles.Batch325.valid13027
  · exact MergedCutProfiles.Batch325.valid13028
  · exact MergedCutProfiles.Batch032.valid1318
  · exact MergedCutProfiles.Batch325.valid13029
  · exact MergedCutProfiles.Batch033.valid1332
  · exact MergedCutProfiles.Batch325.valid13030
  · exact MergedCutProfiles.Batch325.valid13031
  · exact MergedCutProfiles.Batch325.valid13032
  · exact MergedCutProfiles.Batch325.valid13033
  · exact MergedCutProfiles.Batch325.valid13034
  · exact MergedCutProfiles.Batch033.valid1320
theorem numericValid2099 : retention2099.NumericValid := by decide +kernel
def certificate2099 : RatCutBinCertificate := ⟨⟨retention2099,(48332530941006109/25000000000000000),(5353370290855499/200000000000000000),(4507535409253092731/500000000000000000),(315733330643074098997/200000000000000000),(227606287670110173/100000000000000000)⟩,(998805417189520419/1000000000000000000),(246566230245146553/500000000000000000),(158233941249663299/1000000000000000000),(73855432952623757/1000000000000000000)⟩
theorem valid2099 : certificate2099.Valid := by decide +kernel
theorem sound2099 : certificate2099.Sound := rat_cut_bin_certificate_sound certificate2099 profilesValid2099 numericValid2099 valid2099

def certificates : List RatCutBinCertificate := [certificate2088,certificate2089,certificate2090,certificate2091,certificate2092,certificate2093,certificate2094,certificate2095,certificate2096,certificate2097,certificate2098,certificate2099]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound2088,List.forall_mem_cons.mpr ⟨sound2089,List.forall_mem_cons.mpr ⟨sound2090,List.forall_mem_cons.mpr ⟨sound2091,List.forall_mem_cons.mpr ⟨sound2092,List.forall_mem_cons.mpr ⟨sound2093,List.forall_mem_cons.mpr ⟨sound2094,List.forall_mem_cons.mpr ⟨sound2095,List.forall_mem_cons.mpr ⟨sound2096,List.forall_mem_cons.mpr ⟨sound2097,List.forall_mem_cons.mpr ⟨sound2098,List.forall_mem_cons.mpr ⟨sound2099,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch174
