import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch198
import Cycle12.MergedCutProfiles.Batch199
import Cycle12.MergedCutProfiles.Batch200

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch100

def retention1200 : RatCutRetentionCertificate := ⟨(9/160),(113/2000),(6628873081542781369/14383096214428220263),(1806366654373950237/500000000000000000),(6/5),(12097388759828968765754095321248606847/11289791589837188981250000000000000000),false,MergedCutProfiles.Batch198.profile7939,(fun _ => MergedCutProfiles.Batch198.profile7939)⟩
theorem profilesValid1200 : retention1200.ProfilesValid := by
  exact MergedCutProfiles.Batch198.valid7939
theorem numericValid1200 : retention1200.NumericValid := by decide +kernel
def certificate1200 : RatCutBinCertificate := ⟨⟨retention1200,(520705146255523329/200000000000000000),(39612838789917267/250000000000000000),(1853520589949574469/125000000000000000),(106796751771871583253/500000000000000000),(259535665965307127/250000000000000000)⟩,(197940424351025967/200000000000000000),(77451435213242051/200000000000000000),(61340758234435281/250000000000000000),(174949681629648177/1000000000000000000)⟩
theorem valid1200 : certificate1200.Valid := by decide +kernel
theorem sound1200 : certificate1200.Sound := rat_cut_bin_certificate_sound certificate1200 profilesValid1200 numericValid1200 valid1200

def retention1201 : RatCutRetentionCertificate := ⟨(9/160),(113/2000),(7107049175352550317/14383096214428220263),(6628873081542781369/1000000000000000000),(21/20),(10561924638263732170181052191956031510519/10606196930468450190400000000000000000000),false,MergedCutProfiles.Batch198.profile7940,(fun _ => MergedCutProfiles.Batch198.profile7940)⟩
theorem profilesValid1201 : retention1201.ProfilesValid := by
  exact MergedCutProfiles.Batch198.valid7940
theorem numericValid1201 : retention1201.NumericValid := by decide +kernel
def certificate1201 : RatCutBinCertificate := ⟨⟨retention1201,(520705146255523329/200000000000000000),(39612838789917267/250000000000000000),(1853520589949574469/125000000000000000),(106796751771871583253/500000000000000000),(966610800633732739/1000000000000000000)⟩,(197940424351025967/200000000000000000),(207957637188190517/500000000000000000),(219212365790236053/1000000000000000000),(11017009474715817/62500000000000000)⟩
theorem valid1201 : certificate1201.Valid := by decide +kernel
theorem sound1201 : certificate1201.Sound := rat_cut_bin_certificate_sound certificate1201 profilesValid1201 numericValid1201 valid1201

def retention1202 : RatCutRetentionCertificate := ⟨(9/160),(113/2000),(7178119667106075821/14383096214428220263),(7107049175352550317/1000000000000000000),(21/20),(1249173571196394706592012533944074176319/1263475408951564500800000000000000000000),false,MergedCutProfiles.Batch198.profile7941,(fun _ => MergedCutProfiles.Batch198.profile7941)⟩
theorem profilesValid1202 : retention1202.ProfilesValid := by
  exact MergedCutProfiles.Batch198.valid7941
theorem numericValid1202 : retention1202.NumericValid := by decide +kernel
def certificate1202 : RatCutBinCertificate := ⟨⟨retention1202,(520705146255523329/200000000000000000),(39612838789917267/250000000000000000),(1853520589949574469/125000000000000000),(106796751771871583253/500000000000000000),(191893151649134187/200000000000000000)⟩,(197940424351025967/200000000000000000),(1047531381150689/2500000000000000),(54126696233534417/250000000000000000),(10895452269195629/62500000000000000)⟩
theorem valid1202 : certificate1202.Valid := by decide +kernel
theorem sound1202 : certificate1202.Sound := rat_cut_bin_certificate_sound certificate1202 profilesValid1202 numericValid1202 valid1202

def retention1203 : RatCutRetentionCertificate := ⟨(9/160),(113/2000),(1/2),(7178119667106075821/1000000000000000000),(21/20),(11337986305765789097427743695291071779759/11484991467369721313600000000000000000000),false,MergedCutProfiles.Batch198.profile7938,(fun _ => MergedCutProfiles.Batch198.profile7938)⟩
theorem profilesValid1203 : retention1203.ProfilesValid := by
  exact MergedCutProfiles.Batch198.valid7938
theorem numericValid1203 : retention1203.NumericValid := by decide +kernel
def certificate1203 : RatCutBinCertificate := ⟨⟨retention1203,(520705146255523329/200000000000000000),(39612838789917267/250000000000000000),(1853520589949574469/125000000000000000),(106796751771871583253/500000000000000000),(478992733766978019/500000000000000000)⟩,(197940424351025967/200000000000000000),(209830007857870927/500000000000000000),(215944101121231261/1000000000000000000),(86911807708864299/500000000000000000)⟩
theorem valid1203 : certificate1203.Valid := by decide +kernel
theorem sound1203 : certificate1203.Sound := rat_cut_bin_certificate_sound certificate1203 profilesValid1203 numericValid1203 valid1203

def retention1204 : RatCutRetentionCertificate := ⟨(113/2000),(227/4000),(920607525318642211/14235352335483791534),(850165604122726569/1000000000000000000),(14/5),(2567318412855511418693/1280000000000000000000),true,MergedCutProfiles.Batch198.profile7942,![MergedCutProfiles.Batch198.profile7942,MergedCutProfiles.Batch198.profile7943,MergedCutProfiles.Batch198.profile7944,MergedCutProfiles.Batch198.profile7945,MergedCutProfiles.Batch198.profile7946,MergedCutProfiles.Batch198.profile7947,MergedCutProfiles.Batch198.profile7948,MergedCutProfiles.Batch198.profile7949,MergedCutProfiles.Batch198.profile7950,MergedCutProfiles.Batch198.profile7951,MergedCutProfiles.Batch198.profile7952,MergedCutProfiles.Batch198.profile7953,MergedCutProfiles.Batch198.profile7954,MergedCutProfiles.Batch198.profile7955,MergedCutProfiles.Batch198.profile7956,MergedCutProfiles.Batch198.profile7957]⟩
theorem profilesValid1204 : retention1204.ProfilesValid := by
  change ∀ j : Fin 16, (retention1204.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch198.valid7942
  · exact MergedCutProfiles.Batch198.valid7943
  · exact MergedCutProfiles.Batch198.valid7944
  · exact MergedCutProfiles.Batch198.valid7945
  · exact MergedCutProfiles.Batch198.valid7946
  · exact MergedCutProfiles.Batch198.valid7947
  · exact MergedCutProfiles.Batch198.valid7948
  · exact MergedCutProfiles.Batch198.valid7949
  · exact MergedCutProfiles.Batch198.valid7950
  · exact MergedCutProfiles.Batch198.valid7951
  · exact MergedCutProfiles.Batch198.valid7952
  · exact MergedCutProfiles.Batch198.valid7953
  · exact MergedCutProfiles.Batch198.valid7954
  · exact MergedCutProfiles.Batch198.valid7955
  · exact MergedCutProfiles.Batch198.valid7956
  · exact MergedCutProfiles.Batch198.valid7957
theorem numericValid1204 : retention1204.NumericValid := by decide +kernel
def certificate1204 : RatCutBinCertificate := ⟨⟨retention1204,(1133236792796854661/500000000000000000),(160087642728850909/1000000000000000000),(1489382742029792173/100000000000000000),(106168057433297533833/500000000000000000),(968741999988462509/500000000000000000)⟩,(495500772726321197/500000000000000000),(179605029344829343/500000000000000000),(273008992650484009/1000000000000000000),(144788615666065127/1000000000000000000)⟩
theorem valid1204 : certificate1204.Valid := by decide +kernel
theorem sound1204 : certificate1204.Sound := rat_cut_bin_certificate_sound certificate1204 profilesValid1204 numericValid1204 valid1204

def retention1205 : RatCutRetentionCertificate := ⟨(113/2000),(227/4000),(1370659157315326243/14235352335483791534),(920607525318642211/1000000000000000000),(13/5),(611646505381892027879/320000000000000000000),true,MergedCutProfiles.Batch198.profile7958,![MergedCutProfiles.Batch198.profile7958,MergedCutProfiles.Batch198.profile7959,MergedCutProfiles.Batch199.profile7960,MergedCutProfiles.Batch199.profile7961,MergedCutProfiles.Batch199.profile7962,MergedCutProfiles.Batch199.profile7963,MergedCutProfiles.Batch199.profile7964,MergedCutProfiles.Batch199.profile7965,MergedCutProfiles.Batch199.profile7966,MergedCutProfiles.Batch199.profile7967,MergedCutProfiles.Batch199.profile7968,MergedCutProfiles.Batch199.profile7969,MergedCutProfiles.Batch199.profile7970,MergedCutProfiles.Batch199.profile7971,MergedCutProfiles.Batch199.profile7972,MergedCutProfiles.Batch199.profile7973]⟩
theorem profilesValid1205 : retention1205.ProfilesValid := by
  change ∀ j : Fin 16, (retention1205.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch198.valid7958
  · exact MergedCutProfiles.Batch198.valid7959
  · exact MergedCutProfiles.Batch199.valid7960
  · exact MergedCutProfiles.Batch199.valid7961
  · exact MergedCutProfiles.Batch199.valid7962
  · exact MergedCutProfiles.Batch199.valid7963
  · exact MergedCutProfiles.Batch199.valid7964
  · exact MergedCutProfiles.Batch199.valid7965
  · exact MergedCutProfiles.Batch199.valid7966
  · exact MergedCutProfiles.Batch199.valid7967
  · exact MergedCutProfiles.Batch199.valid7968
  · exact MergedCutProfiles.Batch199.valid7969
  · exact MergedCutProfiles.Batch199.valid7970
  · exact MergedCutProfiles.Batch199.valid7971
  · exact MergedCutProfiles.Batch199.valid7972
  · exact MergedCutProfiles.Batch199.valid7973
theorem numericValid1205 : retention1205.NumericValid := by decide +kernel
def certificate1205 : RatCutBinCertificate := ⟨⟨retention1205,(1133236792796854661/500000000000000000),(160087642728850909/1000000000000000000),(1489382742029792173/100000000000000000),(106168057433297533833/500000000000000000),(924017875662385693/500000000000000000)⟩,(495500772726321197/500000000000000000),(364864720529198291/1000000000000000000),(1069057703739483/4000000000000000),(144896640239815107/1000000000000000000)⟩
theorem valid1205 : certificate1205.Valid := by decide +kernel
theorem sound1205 : certificate1205.Sound := rat_cut_bin_certificate_sound certificate1205 profilesValid1205 numericValid1205 valid1205

def retention1206 : RatCutRetentionCertificate := ⟨(113/2000),(227/4000),(3356240798408458701/14235352335483791534),(1370659157315326243/1000000000000000000),(19/10),(1982905440658478541911/1280000000000000000000),true,MergedCutProfiles.Batch199.profile7974,![MergedCutProfiles.Batch199.profile7974,MergedCutProfiles.Batch199.profile7975,MergedCutProfiles.Batch199.profile7976,MergedCutProfiles.Batch199.profile7977,MergedCutProfiles.Batch199.profile7978,MergedCutProfiles.Batch199.profile7979,MergedCutProfiles.Batch199.profile7980,MergedCutProfiles.Batch199.profile7981,MergedCutProfiles.Batch199.profile7982,MergedCutProfiles.Batch199.profile7983,MergedCutProfiles.Batch199.profile7984,MergedCutProfiles.Batch199.profile7985,MergedCutProfiles.Batch199.profile7986,MergedCutProfiles.Batch199.profile7987,MergedCutProfiles.Batch199.profile7988,MergedCutProfiles.Batch199.profile7989]⟩
theorem profilesValid1206 : retention1206.ProfilesValid := by
  change ∀ j : Fin 16, (retention1206.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch199.valid7974
  · exact MergedCutProfiles.Batch199.valid7975
  · exact MergedCutProfiles.Batch199.valid7976
  · exact MergedCutProfiles.Batch199.valid7977
  · exact MergedCutProfiles.Batch199.valid7978
  · exact MergedCutProfiles.Batch199.valid7979
  · exact MergedCutProfiles.Batch199.valid7980
  · exact MergedCutProfiles.Batch199.valid7981
  · exact MergedCutProfiles.Batch199.valid7982
  · exact MergedCutProfiles.Batch199.valid7983
  · exact MergedCutProfiles.Batch199.valid7984
  · exact MergedCutProfiles.Batch199.valid7985
  · exact MergedCutProfiles.Batch199.valid7986
  · exact MergedCutProfiles.Batch199.valid7987
  · exact MergedCutProfiles.Batch199.valid7988
  · exact MergedCutProfiles.Batch199.valid7989
theorem numericValid1206 : retention1206.NumericValid := by decide +kernel
def certificate1206 : RatCutBinCertificate := ⟨⟨retention1206,(1133236792796854661/500000000000000000),(160087642728850909/1000000000000000000),(1489382742029792173/100000000000000000),(106168057433297533833/500000000000000000),(751422412429456671/500000000000000000)⟩,(495500772726321197/500000000000000000),(391501625734874299/1000000000000000000),(60339969211059949/250000000000000000),(18110103588345499/125000000000000000)⟩
theorem valid1206 : certificate1206.Valid := by decide +kernel
theorem sound1206 : certificate1206.Sound := rat_cut_bin_certificate_sound certificate1206 profilesValid1206 numericValid1206 valid1206

def retention1207 : RatCutRetentionCertificate := ⟨(113/2000),(227/4000),(3079122146917650457/7117676167741895767),(3356240798408458701/1000000000000000000),(11/10),(1407682529505926692713/1280000000000000000000),true,MergedCutProfiles.Batch199.profile7990,![MergedCutProfiles.Batch199.profile7990,MergedCutProfiles.Batch199.profile7966,MergedCutProfiles.Batch199.profile7991,MergedCutProfiles.Batch199.profile7992,MergedCutProfiles.Batch199.profile7993,MergedCutProfiles.Batch199.profile7984,MergedCutProfiles.Batch199.profile7994,MergedCutProfiles.Batch199.profile7995,MergedCutProfiles.Batch199.profile7996,MergedCutProfiles.Batch199.profile7997,MergedCutProfiles.Batch199.profile7998,MergedCutProfiles.Batch199.profile7999,MergedCutProfiles.Batch200.profile8000,MergedCutProfiles.Batch200.profile8001,MergedCutProfiles.Batch200.profile8002,MergedCutProfiles.Batch200.profile8003]⟩
theorem profilesValid1207 : retention1207.ProfilesValid := by
  change ∀ j : Fin 16, (retention1207.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch199.valid7990
  · exact MergedCutProfiles.Batch199.valid7966
  · exact MergedCutProfiles.Batch199.valid7991
  · exact MergedCutProfiles.Batch199.valid7992
  · exact MergedCutProfiles.Batch199.valid7993
  · exact MergedCutProfiles.Batch199.valid7984
  · exact MergedCutProfiles.Batch199.valid7994
  · exact MergedCutProfiles.Batch199.valid7995
  · exact MergedCutProfiles.Batch199.valid7996
  · exact MergedCutProfiles.Batch199.valid7997
  · exact MergedCutProfiles.Batch199.valid7998
  · exact MergedCutProfiles.Batch199.valid7999
  · exact MergedCutProfiles.Batch200.valid8000
  · exact MergedCutProfiles.Batch200.valid8001
  · exact MergedCutProfiles.Batch200.valid8002
  · exact MergedCutProfiles.Batch200.valid8003
theorem numericValid1207 : retention1207.NumericValid := by decide +kernel
def certificate1207 : RatCutBinCertificate := ⟨⟨retention1207,(1133236792796854661/500000000000000000),(160087642728850909/1000000000000000000),(1489382742029792173/100000000000000000),(106168057433297533833/500000000000000000),(268237242288549983/250000000000000000)⟩,(495500772726321197/500000000000000000),(225729322164619757/500000000000000000),(189508893529446471/1000000000000000000),(144730760019577261/1000000000000000000)⟩
theorem valid1207 : certificate1207.Valid := by decide +kernel
theorem sound1207 : certificate1207.Sound := rat_cut_bin_certificate_sound certificate1207 profilesValid1207 numericValid1207 valid1207

def retention1208 : RatCutRetentionCertificate := ⟨(113/2000),(227/4000),(6939263811960993555/14235352335483791534),(3079122146917650457/500000000000000000),(11/10),(78508496561503997260004016989042304917/76978053672941261425000000000000000000),false,MergedCutProfiles.Batch200.profile8004,(fun _ => MergedCutProfiles.Batch200.profile8004)⟩
theorem profilesValid1208 : retention1208.ProfilesValid := by
  exact MergedCutProfiles.Batch200.valid8004
theorem numericValid1208 : retention1208.NumericValid := by decide +kernel
def certificate1208 : RatCutBinCertificate := ⟨⟨retention1208,(1133236792796854661/500000000000000000),(160087642728850909/1000000000000000000),(1489382742029792173/100000000000000000),(106168057433297533833/500000000000000000),(248270257801213653/250000000000000000)⟩,(495500772726321197/500000000000000000),(9097644468097741/20000000000000000),(186799195382503219/1000000000000000000),(14736535026041249/100000000000000000)⟩
theorem valid1208 : certificate1208.Valid := by decide +kernel
theorem sound1208 : certificate1208.Sound := rat_cut_bin_certificate_sound certificate1208 profilesValid1208 numericValid1208 valid1208

def retention1209 : RatCutRetentionCertificate := ⟨(113/2000),(227/4000),(3539371507290704763/7117676167741895767),(1387852762392198711/200000000000000000),(21/20),(440279861058853652666595551241481898759/444112883965503587520000000000000000000),false,MergedCutProfiles.Batch200.profile8005,(fun _ => MergedCutProfiles.Batch200.profile8005)⟩
theorem profilesValid1209 : retention1209.ProfilesValid := by
  exact MergedCutProfiles.Batch200.valid8005
theorem numericValid1209 : retention1209.NumericValid := by decide +kernel
def certificate1209 : RatCutBinCertificate := ⟨⟨retention1209,(1133236792796854661/500000000000000000),(160087642728850909/1000000000000000000),(1489382742029792173/100000000000000000),(106168057433297533833/500000000000000000),(965787148217886477/1000000000000000000)⟩,(495500772726321197/500000000000000000),(463178956422031591/1000000000000000000),(180338984486095457/1000000000000000000),(145859480249702783/1000000000000000000)⟩
theorem valid1209 : certificate1209.Valid := by decide +kernel
theorem sound1209 : certificate1209.Sound := rat_cut_bin_certificate_sound certificate1209 profilesValid1209 numericValid1209 valid1209

def retention1210 : RatCutRetentionCertificate := ⟨(113/2000),(227/4000),(1/2),(3539371507290704763/500000000000000000),(21/20),(310449498993367449188683087729810935479/314610800648062645600000000000000000000),false,MergedCutProfiles.Batch200.profile8006,(fun _ => MergedCutProfiles.Batch200.profile8006)⟩
theorem profilesValid1210 : retention1210.ProfilesValid := by
  exact MergedCutProfiles.Batch200.valid8006
theorem numericValid1210 : retention1210.NumericValid := by decide +kernel
def certificate1210 : RatCutBinCertificate := ⟨⟨retention1210,(1133236792796854661/500000000000000000),(160087642728850909/1000000000000000000),(1489382742029792173/100000000000000000),(106168057433297533833/500000000000000000),(240297779161555119/250000000000000000)⟩,(495500772726321197/500000000000000000),(92936413926402891/200000000000000000),(44796142731636343/250000000000000000),(4519775313394577/31250000000000000)⟩
theorem valid1210 : certificate1210.Valid := by decide +kernel
theorem sound1210 : certificate1210.Sound := rat_cut_bin_certificate_sound certificate1210 profilesValid1210 numericValid1210 valid1210

def retention1211 : RatCutRetentionCertificate := ⟨(113/2000),(227/4000),(1/2),64,1,(255403070266455515226198893134174584951/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch200.profile8006,(fun _ => MergedCutProfiles.Batch200.profile8006)⟩
theorem profilesValid1211 : retention1211.ProfilesValid := by
  exact MergedCutProfiles.Batch200.valid8006
theorem numericValid1211 : retention1211.NumericValid := by decide +kernel
def certificate1211 : RatCutBinCertificate := ⟨⟨retention1211,(1133236792796854661/500000000000000000),(160087642728850909/1000000000000000000),(1489382742029792173/100000000000000000),(106168057433297533833/500000000000000000),(973306561193191063/1000000000000000000)⟩,(495500772726321197/500000000000000000),(427801537323269819/1000000000000000000),(20895336705718179/100000000000000000),(99254810087500849/500000000000000000)⟩
theorem valid1211 : certificate1211.Valid := by decide +kernel
theorem sound1211 : certificate1211.Sound := rat_cut_bin_certificate_sound certificate1211 profilesValid1211 numericValid1211 valid1211

def certificates : List RatCutBinCertificate := [certificate1200,certificate1201,certificate1202,certificate1203,certificate1204,certificate1205,certificate1206,certificate1207,certificate1208,certificate1209,certificate1210,certificate1211]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound1200,List.forall_mem_cons.mpr ⟨sound1201,List.forall_mem_cons.mpr ⟨sound1202,List.forall_mem_cons.mpr ⟨sound1203,List.forall_mem_cons.mpr ⟨sound1204,List.forall_mem_cons.mpr ⟨sound1205,List.forall_mem_cons.mpr ⟨sound1206,List.forall_mem_cons.mpr ⟨sound1207,List.forall_mem_cons.mpr ⟨sound1208,List.forall_mem_cons.mpr ⟨sound1209,List.forall_mem_cons.mpr ⟨sound1210,List.forall_mem_cons.mpr ⟨sound1211,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch100
