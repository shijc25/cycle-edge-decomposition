import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch200
import Cycle12.MergedCutProfiles.Batch201

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch101

def retention1212 : RatCutRetentionCertificate := ⟨(113/2000),(227/4000),(3286695798163977101/7117676167741895767),(1809160439803610679/500000000000000000),(6/5),(387123432633059371222995512042029216271/361832087960722135800000000000000000000),false,MergedCutProfiles.Batch200.profile8007,(fun _ => MergedCutProfiles.Batch200.profile8007)⟩
theorem profilesValid1212 : retention1212.ProfilesValid := by
  exact MergedCutProfiles.Batch200.valid8007
theorem numericValid1212 : retention1212.NumericValid := by decide +kernel
def certificate1212 : RatCutBinCertificate := ⟨⟨retention1212,(1303212243796854661/500000000000000000),(160087642728850909/1000000000000000000),(1489382742029792173/100000000000000000),(106168057433297533833/500000000000000000),(259068427995710379/250000000000000000)⟩,(61853076739994291/62500000000000000),(193302514541986277/500000000000000000),(245982213605853281/1000000000000000000),(87581131826842387/500000000000000000)⟩
theorem valid1212 : certificate1212.Valid := by decide +kernel
theorem sound1212 : certificate1212.Sound := rat_cut_bin_certificate_sound certificate1212 profilesValid1212 numericValid1212 valid1212

def retention1213 : RatCutRetentionCertificate := ⟨(113/2000),(227/4000),(7047565513666331725/14235352335483791534),(3286695798163977101/500000000000000000),(21/20),(2612867146073184749447655746407765422159/2629356638531181680800000000000000000000),false,MergedCutProfiles.Batch200.profile8008,(fun _ => MergedCutProfiles.Batch200.profile8008)⟩
theorem profilesValid1213 : retention1213.ProfilesValid := by
  exact MergedCutProfiles.Batch200.valid8008
theorem numericValid1213 : retention1213.NumericValid := by decide +kernel
def certificate1213 : RatCutBinCertificate := ⟨⟨retention1213,(1303212243796854661/500000000000000000),(160087642728850909/1000000000000000000),(1489382742029792173/100000000000000000),(106168057433297533833/500000000000000000),(964309326395882963/1000000000000000000)⟩,(61853076739994291/62500000000000000),(415456552782120943/1000000000000000000),(219615031425494729/1000000000000000000),(44010003480348737/250000000000000000)⟩
theorem valid1213 : certificate1213.Valid := by decide +kernel
theorem sound1213 : certificate1213.Sound := rat_cut_bin_certificate_sound certificate1213 profilesValid1213 numericValid1213 valid1213

def retention1214 : RatCutRetentionCertificate := ⟨(113/2000),(227/4000),(1/2),(281902620546653269/40000000000000000),(21/20),(445016405811016500934008329472459072071/451044192874645230400000000000000000000),false,MergedCutProfiles.Batch200.profile8006,(fun _ => MergedCutProfiles.Batch200.profile8006)⟩
theorem profilesValid1214 : retention1214.ProfilesValid := by
  exact MergedCutProfiles.Batch200.valid8006
theorem numericValid1214 : retention1214.NumericValid := by decide +kernel
def certificate1214 : RatCutBinCertificate := ⟨⟨retention1214,(1303212243796854661/500000000000000000),(160087642728850909/1000000000000000000),(1489382742029792173/100000000000000000),(106168057433297533833/500000000000000000),(478608386853387253/500000000000000000)⟩,(61853076739994291/62500000000000000),(209267450991622377/500000000000000000),(108461266211441707/500000000000000000),(87063054964845187/500000000000000000)⟩
theorem valid1214 : certificate1214.Valid := by decide +kernel
theorem sound1214 : certificate1214.Sound := rat_cut_bin_certificate_sound certificate1214 profilesValid1214 numericValid1214 valid1214

def retention1215 : RatCutRetentionCertificate := ⟨(227/4000),(57/1000),(460300347912784474/7044818956914543545),(106269912150056919/125000000000000000),(14/5),(320719451050358864553/160000000000000000000),true,MergedCutProfiles.Batch200.profile8009,![MergedCutProfiles.Batch200.profile8009,MergedCutProfiles.Batch200.profile8010,MergedCutProfiles.Batch200.profile8011,MergedCutProfiles.Batch200.profile8012,MergedCutProfiles.Batch200.profile8013,MergedCutProfiles.Batch200.profile8014,MergedCutProfiles.Batch200.profile8015,MergedCutProfiles.Batch200.profile8016,MergedCutProfiles.Batch200.profile8017,MergedCutProfiles.Batch200.profile8018,MergedCutProfiles.Batch200.profile8019,MergedCutProfiles.Batch200.profile8020,MergedCutProfiles.Batch200.profile8021,MergedCutProfiles.Batch200.profile8022,MergedCutProfiles.Batch200.profile8023,MergedCutProfiles.Batch200.profile8024]⟩
theorem profilesValid1215 : retention1215.ProfilesValid := by
  change ∀ j : Fin 16, (retention1215.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch200.valid8009
  · exact MergedCutProfiles.Batch200.valid8010
  · exact MergedCutProfiles.Batch200.valid8011
  · exact MergedCutProfiles.Batch200.valid8012
  · exact MergedCutProfiles.Batch200.valid8013
  · exact MergedCutProfiles.Batch200.valid8014
  · exact MergedCutProfiles.Batch200.valid8015
  · exact MergedCutProfiles.Batch200.valid8016
  · exact MergedCutProfiles.Batch200.valid8017
  · exact MergedCutProfiles.Batch200.valid8018
  · exact MergedCutProfiles.Batch200.valid8019
  · exact MergedCutProfiles.Batch200.valid8020
  · exact MergedCutProfiles.Batch200.valid8021
  · exact MergedCutProfiles.Batch200.valid8022
  · exact MergedCutProfiles.Batch200.valid8023
  · exact MergedCutProfiles.Batch200.valid8024
theorem numericValid1215 : retention1215.NumericValid := by decide +kernel
def certificate1215 : RatCutBinCertificate := ⟨⟨retention1215,(2271141721695265191/1000000000000000000),(161735409484216873/1000000000000000000),(14959933277224716671/1000000000000000000),(211095948276747537531/1000000000000000000),(7742894584875557/4000000000000000)⟩,(990947375847312209/1000000000000000000),(358377709207377139/1000000000000000000),(273862049150398799/1000000000000000000),(72564314432677019/500000000000000000)⟩
theorem valid1215 : certificate1215.Valid := by decide +kernel
theorem sound1215 : certificate1215.Sound := rat_cut_bin_certificate_sound certificate1215 profilesValid1215 numericValid1215 valid1215

def retention1216 : RatCutRetentionCertificate := ⟨(227/4000),(57/1000),(274129797826154135/2817927582765817418),(230150173956392237/250000000000000000),(13/5),(152728252011259016783/80000000000000000000),true,MergedCutProfiles.Batch200.profile8025,![MergedCutProfiles.Batch200.profile8025,MergedCutProfiles.Batch200.profile8026,MergedCutProfiles.Batch200.profile8027,MergedCutProfiles.Batch200.profile8028,MergedCutProfiles.Batch200.profile8029,MergedCutProfiles.Batch200.profile8030,MergedCutProfiles.Batch200.profile8031,MergedCutProfiles.Batch200.profile8032,MergedCutProfiles.Batch200.profile8033,MergedCutProfiles.Batch200.profile8034,MergedCutProfiles.Batch200.profile8035,MergedCutProfiles.Batch200.profile8036,MergedCutProfiles.Batch200.profile8037,MergedCutProfiles.Batch200.profile8038,MergedCutProfiles.Batch200.profile8039,MergedCutProfiles.Batch201.profile8040]⟩
theorem profilesValid1216 : retention1216.ProfilesValid := by
  change ∀ j : Fin 16, (retention1216.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch200.valid8025
  · exact MergedCutProfiles.Batch200.valid8026
  · exact MergedCutProfiles.Batch200.valid8027
  · exact MergedCutProfiles.Batch200.valid8028
  · exact MergedCutProfiles.Batch200.valid8029
  · exact MergedCutProfiles.Batch200.valid8030
  · exact MergedCutProfiles.Batch200.valid8031
  · exact MergedCutProfiles.Batch200.valid8032
  · exact MergedCutProfiles.Batch200.valid8033
  · exact MergedCutProfiles.Batch200.valid8034
  · exact MergedCutProfiles.Batch200.valid8035
  · exact MergedCutProfiles.Batch200.valid8036
  · exact MergedCutProfiles.Batch200.valid8037
  · exact MergedCutProfiles.Batch200.valid8038
  · exact MergedCutProfiles.Batch200.valid8039
  · exact MergedCutProfiles.Batch201.valid8040
theorem numericValid1216 : retention1216.NumericValid := by decide +kernel
def certificate1216 : RatCutBinCertificate := ⟨⟨retention1216,(2271141721695265191/1000000000000000000),(161735409484216873/1000000000000000000),(14959933277224716671/1000000000000000000),(211095948276747537531/1000000000000000000),(184524269151918633/100000000000000000)⟩,(990947375847312209/1000000000000000000),(364237568928791057/1000000000000000000),(267897208030563267/1000000000000000000),(29012047955493393/200000000000000000)⟩
theorem valid1216 : certificate1216.Valid := by decide +kernel
theorem sound1216 : certificate1216.Sound := rat_cut_bin_certificate_sound certificate1216 profilesValid1216 numericValid1216 valid1216

def retention1217 : RatCutRetentionCertificate := ⟨(227/4000),(57/1000),(1678107950129757039/7044818956914543545),(54825959565230827/40000000000000000),(37/20),(78832766873410838419/51200000000000000000),true,MergedCutProfiles.Batch201.profile8041,![MergedCutProfiles.Batch201.profile8041,MergedCutProfiles.Batch201.profile8042,MergedCutProfiles.Batch201.profile8043,MergedCutProfiles.Batch201.profile8044,MergedCutProfiles.Batch201.profile8045,MergedCutProfiles.Batch201.profile8046,MergedCutProfiles.Batch201.profile8047,MergedCutProfiles.Batch201.profile8048,MergedCutProfiles.Batch201.profile8049,MergedCutProfiles.Batch201.profile8050,MergedCutProfiles.Batch201.profile8051,MergedCutProfiles.Batch201.profile8052,MergedCutProfiles.Batch201.profile8053,MergedCutProfiles.Batch201.profile8054,MergedCutProfiles.Batch201.profile8055,MergedCutProfiles.Batch201.profile8056]⟩
theorem profilesValid1217 : retention1217.ProfilesValid := by
  change ∀ j : Fin 16, (retention1217.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch201.valid8041
  · exact MergedCutProfiles.Batch201.valid8042
  · exact MergedCutProfiles.Batch201.valid8043
  · exact MergedCutProfiles.Batch201.valid8044
  · exact MergedCutProfiles.Batch201.valid8045
  · exact MergedCutProfiles.Batch201.valid8046
  · exact MergedCutProfiles.Batch201.valid8047
  · exact MergedCutProfiles.Batch201.valid8048
  · exact MergedCutProfiles.Batch201.valid8049
  · exact MergedCutProfiles.Batch201.valid8050
  · exact MergedCutProfiles.Batch201.valid8051
  · exact MergedCutProfiles.Batch201.valid8052
  · exact MergedCutProfiles.Batch201.valid8053
  · exact MergedCutProfiles.Batch201.valid8054
  · exact MergedCutProfiles.Batch201.valid8055
  · exact MergedCutProfiles.Batch201.valid8056
theorem numericValid1217 : retention1217.NumericValid := by decide +kernel
def certificate1217 : RatCutBinCertificate := ⟨⟨retention1217,(2271141721695265191/1000000000000000000),(161735409484216873/1000000000000000000),(14959933277224716671/1000000000000000000),(211095948276747537531/1000000000000000000),(373566030142553319/250000000000000000)⟩,(990947375847312209/1000000000000000000),(392471550431954283/1000000000000000000),(30056445626139699/125000000000000000),(145721009228623567/1000000000000000000)⟩
theorem valid1217 : certificate1217.Valid := by decide +kernel
theorem sound1217 : certificate1217.Sound := rat_cut_bin_certificate_sound certificate1217 profilesValid1217 numericValid1217 valid1217

def retention1218 : RatCutRetentionCertificate := ⟨(227/4000),(57/1000),(469017411205366563/1083818301063775930),(1678107950129757039/500000000000000000),(11/10),(703844609346334286907/640000000000000000000),true,MergedCutProfiles.Batch201.profile8057,![MergedCutProfiles.Batch201.profile8057,MergedCutProfiles.Batch201.profile8058,MergedCutProfiles.Batch201.profile8059,MergedCutProfiles.Batch201.profile8060,MergedCutProfiles.Batch201.profile8061,MergedCutProfiles.Batch201.profile8062,MergedCutProfiles.Batch201.profile8063,MergedCutProfiles.Batch201.profile8064,MergedCutProfiles.Batch201.profile8065,MergedCutProfiles.Batch201.profile8066,MergedCutProfiles.Batch201.profile8067,MergedCutProfiles.Batch201.profile8068,MergedCutProfiles.Batch201.profile8069,MergedCutProfiles.Batch201.profile8070,MergedCutProfiles.Batch201.profile8071,MergedCutProfiles.Batch201.profile8072]⟩
theorem profilesValid1218 : retention1218.ProfilesValid := by
  change ∀ j : Fin 16, (retention1218.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch201.valid8057
  · exact MergedCutProfiles.Batch201.valid8058
  · exact MergedCutProfiles.Batch201.valid8059
  · exact MergedCutProfiles.Batch201.valid8060
  · exact MergedCutProfiles.Batch201.valid8061
  · exact MergedCutProfiles.Batch201.valid8062
  · exact MergedCutProfiles.Batch201.valid8063
  · exact MergedCutProfiles.Batch201.valid8064
  · exact MergedCutProfiles.Batch201.valid8065
  · exact MergedCutProfiles.Batch201.valid8066
  · exact MergedCutProfiles.Batch201.valid8067
  · exact MergedCutProfiles.Batch201.valid8068
  · exact MergedCutProfiles.Batch201.valid8069
  · exact MergedCutProfiles.Batch201.valid8070
  · exact MergedCutProfiles.Batch201.valid8071
  · exact MergedCutProfiles.Batch201.valid8072
theorem numericValid1218 : retention1218.NumericValid := by decide +kernel
def certificate1218 : RatCutBinCertificate := ⟨⟨retention1218,(2271141721695265191/1000000000000000000),(161735409484216873/1000000000000000000),(14959933277224716671/1000000000000000000),(211095948276747537531/1000000000000000000),(536371178034860383/500000000000000000)⟩,(990947375847312209/1000000000000000000),(450065495008810433/1000000000000000000),(19061896484542671/100000000000000000),(72773456790418737/500000000000000000)⟩
theorem valid1218 : certificate1218.Valid := by decide +kernel
theorem sound1218 : certificate1218.Sound := rat_cut_bin_certificate_sound certificate1218 profilesValid1218 numericValid1218 valid1218

def retention1219 : RatCutRetentionCertificate := ⟨(227/4000),(57/1000),(687050726068077294/1408963791382908709),(6097226345669765319/1000000000000000000),(11/10),(828648773525659391851165454574930402813/812963512755968709200000000000000000000),false,MergedCutProfiles.Batch201.profile8073,(fun _ => MergedCutProfiles.Batch201.profile8073)⟩
theorem profilesValid1219 : retention1219.ProfilesValid := by
  exact MergedCutProfiles.Batch201.valid8073
theorem numericValid1219 : retention1219.NumericValid := by decide +kernel
def certificate1219 : RatCutBinCertificate := ⟨⟨retention1219,(2271141721695265191/1000000000000000000),(161735409484216873/1000000000000000000),(14959933277224716671/1000000000000000000),(211095948276747537531/1000000000000000000),(992281603392793079/1000000000000000000)⟩,(990947375847312209/1000000000000000000),(56767947091377029/125000000000000000),(187381633923012611/1000000000000000000),(73768253838312121/500000000000000000)⟩
theorem valid1219 : certificate1219.Valid := by decide +kernel
theorem sound1219 : certificate1219.Sound := rat_cut_bin_certificate_sound certificate1219 profilesValid1219 numericValid1219 valid1219

def retention1220 : RatCutRetentionCertificate := ⟨(227/4000),(57/1000),(7008604456620456477/14089637913829087090),(343525363034038647/50000000000000000),(21/20),(972406209758308073418865302350410853/981501037240110420000000000000000000),false,MergedCutProfiles.Batch201.profile8074,(fun _ => MergedCutProfiles.Batch201.profile8074)⟩
theorem profilesValid1220 : retention1220.ProfilesValid := by
  exact MergedCutProfiles.Batch201.valid8074
theorem numericValid1220 : retention1220.NumericValid := by decide +kernel
def certificate1220 : RatCutBinCertificate := ⟨⟨retention1220,(2271141721695265191/1000000000000000000),(161735409484216873/1000000000000000000),(14959933277224716671/1000000000000000000),(211095948276747537531/1000000000000000000),(120618683807948279/125000000000000000)⟩,(990947375847312209/1000000000000000000),(231206639451933609/500000000000000000),(22616113805258767/125000000000000000),(73025303257281043/500000000000000000)⟩
theorem valid1220 : certificate1220.Valid := by decide +kernel
theorem sound1220 : certificate1220.Sound := rat_cut_bin_certificate_sound certificate1220 profilesValid1220 numericValid1220 valid1220

def retention1221 : RatCutRetentionCertificate := ⟨(227/4000),(57/1000),(1/2),(7008604456620456477/1000000000000000000),(21/20),(1229108351329660992720535814099080250999/1245974125621414484800000000000000000000),false,MergedCutProfiles.Batch201.profile8075,(fun _ => MergedCutProfiles.Batch201.profile8075)⟩
theorem profilesValid1221 : retention1221.ProfilesValid := by
  exact MergedCutProfiles.Batch201.valid8075
theorem numericValid1221 : retention1221.NumericValid := by decide +kernel
def certificate1221 : RatCutBinCertificate := ⟨⟨retention1221,(2271141721695265191/1000000000000000000),(161735409484216873/1000000000000000000),(14959933277224716671/1000000000000000000),(211095948276747537531/1000000000000000000),(480339776136356681/500000000000000000)⟩,(990947375847312209/1000000000000000000),(463751666972811037/1000000000000000000),(89949279931600363/500000000000000000),(3624294906486421/25000000000000000)⟩
theorem valid1221 : certificate1221.Valid := by decide +kernel
theorem sound1221 : certificate1221.Sound := rat_cut_bin_certificate_sound certificate1221 profilesValid1221 numericValid1221 valid1221

def retention1222 : RatCutRetentionCertificate := ⟨(227/4000),(57/1000),(1/2),64,1,(255403424290683979066822512033815938479/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch201.profile8075,(fun _ => MergedCutProfiles.Batch201.profile8075)⟩
theorem profilesValid1222 : retention1222.ProfilesValid := by
  exact MergedCutProfiles.Batch201.valid8075
theorem numericValid1222 : retention1222.NumericValid := by decide +kernel
def certificate1222 : RatCutBinCertificate := ⟨⟨retention1222,(2271141721695265191/1000000000000000000),(161735409484216873/1000000000000000000),(14959933277224716671/1000000000000000000),(211095948276747537531/1000000000000000000),(973115476933475899/1000000000000000000)⟩,(990947375847312209/1000000000000000000),(85294100283064813/200000000000000000),(210085592585512463/1000000000000000000),(99767813659687849/500000000000000000)⟩
theorem valid1222 : certificate1222.Valid := by decide +kernel
theorem sound1222 : certificate1222.Sound := rat_cut_bin_certificate_sound certificate1222 profilesValid1222 numericValid1222 valid1222

def retention1223 : RatCutRetentionCertificate := ⟨(227/4000),(57/1000),(6514530258763630581/14089637913829087090),(1810889942870435071/500000000000000000),(6/5),(387092415480882085614459362739435759551/362177988574087014200000000000000000000),false,MergedCutProfiles.Batch201.profile8076,(fun _ => MergedCutProfiles.Batch201.profile8076)⟩
theorem profilesValid1223 : retention1223.ProfilesValid := by
  exact MergedCutProfiles.Batch201.valid8076
theorem numericValid1223 : retention1223.NumericValid := by decide +kernel
def certificate1223 : RatCutBinCertificate := ⟨⟨retention1223,(2609683666695265191/1000000000000000000),(161735409484216873/1000000000000000000),(14959933277224716671/1000000000000000000),(211095948276747537531/1000000000000000000),(517463948271016447/500000000000000000)⟩,(989595294535436387/1000000000000000000),(192903730297717933/500000000000000000),(246740959253518241/1000000000000000000),(43882287531256907/250000000000000000)⟩
theorem valid1223 : certificate1223.Valid := by decide +kernel
theorem sound1223 : certificate1223.Sound := rat_cut_bin_certificate_sound certificate1223 profilesValid1223 numericValid1223 valid1223

def certificates : List RatCutBinCertificate := [certificate1212,certificate1213,certificate1214,certificate1215,certificate1216,certificate1217,certificate1218,certificate1219,certificate1220,certificate1221,certificate1222,certificate1223]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound1212,List.forall_mem_cons.mpr ⟨sound1213,List.forall_mem_cons.mpr ⟨sound1214,List.forall_mem_cons.mpr ⟨sound1215,List.forall_mem_cons.mpr ⟨sound1216,List.forall_mem_cons.mpr ⟨sound1217,List.forall_mem_cons.mpr ⟨sound1218,List.forall_mem_cons.mpr ⟨sound1219,List.forall_mem_cons.mpr ⟨sound1220,List.forall_mem_cons.mpr ⟨sound1221,List.forall_mem_cons.mpr ⟨sound1222,List.forall_mem_cons.mpr ⟨sound1223,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch101
