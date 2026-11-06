import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch150
import Cycle12.MergedCutProfiles.Batch151
import Cycle12.MergedCutProfiles.Batch152

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch074

def retention888 : RatCutRetentionCertificate := ⟨(99/2000),(199/4000),(1080996638948893689/19297355914231360480),(868468599062609361/1000000000000000000),(57/20),(2608898568033276878889/1280000000000000000000),true,MergedCutProfiles.Batch150.profile6015,![MergedCutProfiles.Batch150.profile6015,MergedCutProfiles.Batch150.profile6016,MergedCutProfiles.Batch150.profile6017,MergedCutProfiles.Batch150.profile6003,MergedCutProfiles.Batch150.profile6018,MergedCutProfiles.Batch150.profile6019,MergedCutProfiles.Batch150.profile6020,MergedCutProfiles.Batch150.profile6021,MergedCutProfiles.Batch150.profile6022,MergedCutProfiles.Batch150.profile6023,MergedCutProfiles.Batch150.profile6024,MergedCutProfiles.Batch150.profile6025,MergedCutProfiles.Batch150.profile6026,MergedCutProfiles.Batch150.profile6027,MergedCutProfiles.Batch150.profile6028,MergedCutProfiles.Batch150.profile6029]⟩
theorem profilesValid888 : retention888.ProfilesValid := by
  change ∀ j : Fin 16, (retention888.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch150.valid6015
  · exact MergedCutProfiles.Batch150.valid6016
  · exact MergedCutProfiles.Batch150.valid6017
  · exact MergedCutProfiles.Batch150.valid6003
  · exact MergedCutProfiles.Batch150.valid6018
  · exact MergedCutProfiles.Batch150.valid6019
  · exact MergedCutProfiles.Batch150.valid6020
  · exact MergedCutProfiles.Batch150.valid6021
  · exact MergedCutProfiles.Batch150.valid6022
  · exact MergedCutProfiles.Batch150.valid6023
  · exact MergedCutProfiles.Batch150.valid6024
  · exact MergedCutProfiles.Batch150.valid6025
  · exact MergedCutProfiles.Batch150.valid6026
  · exact MergedCutProfiles.Batch150.valid6027
  · exact MergedCutProfiles.Batch150.valid6028
  · exact MergedCutProfiles.Batch150.valid6029
theorem numericValid888 : retention888.NumericValid := by decide +kernel
def certificate888 : RatCutBinCertificate := ⟨⟨retention888,(1071187279941295167/500000000000000000),(29595609602345631/250000000000000000),(3302378788223152359/250000000000000000),(255273060558360408829/1000000000000000000),(991736218553684879/500000000000000000)⟩,(248145578385063119/250000000000000000),(93893596405956633/250000000000000000),(256623313376583963/1000000000000000000),(8635961036800031/62500000000000000)⟩
theorem valid888 : certificate888.Valid := by decide +kernel
theorem sound888 : certificate888.Sound := rat_cut_bin_certificate_sound certificate888 profilesValid888 numericValid888 valid888

def retention889 : RatCutRetentionCertificate := ⟨(99/2000),(199/4000),(1297404024760046351/9648677957115680240),(1080996638948893689/1000000000000000000),(47/20),(2304377403834023151657/1280000000000000000000),true,MergedCutProfiles.Batch150.profile6030,![MergedCutProfiles.Batch150.profile6030,MergedCutProfiles.Batch150.profile6031,MergedCutProfiles.Batch150.profile6007,MergedCutProfiles.Batch150.profile6032,MergedCutProfiles.Batch150.profile6025,MergedCutProfiles.Batch150.profile6033,MergedCutProfiles.Batch150.profile6034,MergedCutProfiles.Batch150.profile6035,MergedCutProfiles.Batch150.profile6036,MergedCutProfiles.Batch150.profile6037,MergedCutProfiles.Batch150.profile6038,MergedCutProfiles.Batch150.profile6039,MergedCutProfiles.Batch151.profile6040,MergedCutProfiles.Batch151.profile6041,MergedCutProfiles.Batch151.profile6042,MergedCutProfiles.Batch151.profile6043]⟩
theorem profilesValid889 : retention889.ProfilesValid := by
  change ∀ j : Fin 16, (retention889.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch150.valid6030
  · exact MergedCutProfiles.Batch150.valid6031
  · exact MergedCutProfiles.Batch150.valid6007
  · exact MergedCutProfiles.Batch150.valid6032
  · exact MergedCutProfiles.Batch150.valid6025
  · exact MergedCutProfiles.Batch150.valid6033
  · exact MergedCutProfiles.Batch150.valid6034
  · exact MergedCutProfiles.Batch150.valid6035
  · exact MergedCutProfiles.Batch150.valid6036
  · exact MergedCutProfiles.Batch150.valid6037
  · exact MergedCutProfiles.Batch150.valid6038
  · exact MergedCutProfiles.Batch150.valid6039
  · exact MergedCutProfiles.Batch151.valid6040
  · exact MergedCutProfiles.Batch151.valid6041
  · exact MergedCutProfiles.Batch151.valid6042
  · exact MergedCutProfiles.Batch151.valid6043
theorem numericValid889 : retention889.NumericValid := by decide +kernel
def certificate889 : RatCutBinCertificate := ⟨⟨retention889,(1071187279941295167/500000000000000000),(29595609602345631/250000000000000000),(3302378788223152359/250000000000000000),(255273060558360408829/1000000000000000000),(2808267477394403/1600000000000000)⟩,(248145578385063119/250000000000000000),(97722769176788521/250000000000000000),(241932873044482093/1000000000000000000),(6920906083566539/50000000000000000)⟩
theorem valid889 : certificate889.Valid := by decide +kernel
theorem sound889 : certificate889.Sound := rat_cut_bin_certificate_sound certificate889 profilesValid889 numericValid889 valid889

def retention890 : RatCutRetentionCertificate := ⟨(99/2000),(199/4000),(1789885999561667857/4824338978557840120),(1297404024760046351/500000000000000000),(13/10),(796404715400161290979/640000000000000000000),true,MergedCutProfiles.Batch151.profile6044,![MergedCutProfiles.Batch151.profile6044,MergedCutProfiles.Batch151.profile6045,MergedCutProfiles.Batch151.profile6046,MergedCutProfiles.Batch151.profile6047,MergedCutProfiles.Batch151.profile6048,MergedCutProfiles.Batch151.profile6049,MergedCutProfiles.Batch151.profile6050,MergedCutProfiles.Batch151.profile6051,MergedCutProfiles.Batch151.profile6052,MergedCutProfiles.Batch151.profile6053,MergedCutProfiles.Batch151.profile6054,MergedCutProfiles.Batch151.profile6055,MergedCutProfiles.Batch151.profile6056,MergedCutProfiles.Batch151.profile6057,MergedCutProfiles.Batch151.profile6058,MergedCutProfiles.Batch151.profile6059]⟩
theorem profilesValid890 : retention890.ProfilesValid := by
  change ∀ j : Fin 16, (retention890.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch151.valid6044
  · exact MergedCutProfiles.Batch151.valid6045
  · exact MergedCutProfiles.Batch151.valid6046
  · exact MergedCutProfiles.Batch151.valid6047
  · exact MergedCutProfiles.Batch151.valid6048
  · exact MergedCutProfiles.Batch151.valid6049
  · exact MergedCutProfiles.Batch151.valid6050
  · exact MergedCutProfiles.Batch151.valid6051
  · exact MergedCutProfiles.Batch151.valid6052
  · exact MergedCutProfiles.Batch151.valid6053
  · exact MergedCutProfiles.Batch151.valid6054
  · exact MergedCutProfiles.Batch151.valid6055
  · exact MergedCutProfiles.Batch151.valid6056
  · exact MergedCutProfiles.Batch151.valid6057
  · exact MergedCutProfiles.Batch151.valid6058
  · exact MergedCutProfiles.Batch151.valid6059
theorem numericValid890 : retention890.NumericValid := by decide +kernel
def certificate890 : RatCutBinCertificate := ⟨⟨retention890,(1071187279941295167/500000000000000000),(29595609602345631/250000000000000000),(3302378788223152359/250000000000000000),(255273060558360408829/1000000000000000000),(1219419248033350099/1000000000000000000)⟩,(248145578385063119/250000000000000000),(223775440837013729/500000000000000000),(24079193893842209/125000000000000000),(17523383256041413/125000000000000000)⟩
theorem valid890 : certificate890.Valid := by decide +kernel
theorem sound890 : certificate890.Sound := rat_cut_bin_certificate_sound certificate890 profilesValid890 numericValid890 valid890

def retention891 : RatCutRetentionCertificate := ⟨(99/2000),(199/4000),(9273444576015991573/19297355914231360480),(1789885999561667857/250000000000000000),(21/20),(5729465662103533882456631308059459427/5593393748630212053125000000000000000),false,MergedCutProfiles.Batch151.profile6060,(fun _ => MergedCutProfiles.Batch151.profile6060)⟩
theorem profilesValid891 : retention891.ProfilesValid := by
  exact MergedCutProfiles.Batch151.valid6060
theorem numericValid891 : retention891.NumericValid := by decide +kernel
def certificate891 : RatCutBinCertificate := ⟨⟨retention891,(1071187279941295167/500000000000000000),(29595609602345631/250000000000000000),(3302378788223152359/250000000000000000),(255273060558360408829/1000000000000000000),(251041565652558869/250000000000000000)⟩,(248145578385063119/250000000000000000),(19194567954387433/40000000000000000),(83897193241784213/500000000000000000),(141230069145440233/1000000000000000000)⟩
theorem valid891 : certificate891.Valid := by decide +kernel
theorem sound891 : certificate891.Sound := rat_cut_bin_certificate_sound certificate891 profilesValid891 numericValid891 valid891

def retention892 : RatCutRetentionCertificate := ⟨(99/2000),(199/4000),(1910887844022770427/3859471182846272096),(9273444576015991573/1000000000000000000),(21/20),(14885783013820091470981615039061417749391/14837511321625586516800000000000000000000),false,MergedCutProfiles.Batch151.profile6061,(fun _ => MergedCutProfiles.Batch151.profile6061)⟩
theorem profilesValid892 : retention892.ProfilesValid := by
  exact MergedCutProfiles.Batch151.valid6061
theorem numericValid892 : retention892.NumericValid := by decide +kernel
def certificate892 : RatCutBinCertificate := ⟨⟨retention892,(1071187279941295167/500000000000000000),(29595609602345631/250000000000000000),(3302378788223152359/250000000000000000),(255273060558360408829/1000000000000000000),(2457731616487001/2500000000000000)⟩,(248145578385063119/250000000000000000),(96345921050714433/200000000000000000),(166428335302575447/1000000000000000000),(14104162641013293/100000000000000000)⟩
theorem valid892 : certificate892.Valid := by decide +kernel
theorem sound892 : certificate892.Sound := rat_cut_bin_certificate_sound certificate892 profilesValid892 numericValid892 valid892

def retention893 : RatCutRetentionCertificate := ⟨(99/2000),(199/4000),(1/2),(1910887844022770427/200000000000000000),(21/20),(4504017056409412010749789227791974137/4529511926572492864000000000000000000),false,MergedCutProfiles.Batch151.profile6062,(fun _ => MergedCutProfiles.Batch151.profile6062)⟩
theorem profilesValid893 : retention893.ProfilesValid := by
  exact MergedCutProfiles.Batch151.valid6062
theorem numericValid893 : retention893.NumericValid := by decide +kernel
def certificate893 : RatCutBinCertificate := ⟨⟨retention893,(1071187279941295167/500000000000000000),(29595609602345631/250000000000000000),(3302378788223152359/250000000000000000),(255273060558360408829/1000000000000000000),(97421070669631003/100000000000000000)⟩,(248145578385063119/250000000000000000),(242637560320544527/500000000000000000),(81925907848936773/500000000000000000),(138067469331714649/1000000000000000000)⟩
theorem valid893 : certificate893.Valid := by decide +kernel
theorem sound893 : certificate893.Sound := rat_cut_bin_certificate_sound certificate893 profilesValid893 numericValid893 valid893

def retention894 : RatCutRetentionCertificate := ⟨(99/2000),(199/4000),(1/2),64,1,(255394007314836853054004608177815136551/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch151.profile6062,(fun _ => MergedCutProfiles.Batch151.profile6062)⟩
theorem profilesValid894 : retention894.ProfilesValid := by
  exact MergedCutProfiles.Batch151.valid6062
theorem numericValid894 : retention894.NumericValid := by decide +kernel
def certificate894 : RatCutBinCertificate := ⟨⟨retention894,(1071187279941295167/500000000000000000),(29595609602345631/250000000000000000),(3302378788223152359/250000000000000000),(255273060558360408829/1000000000000000000),(978432941668223053/1000000000000000000)⟩,(248145578385063119/250000000000000000),(114879835742923579/250000000000000000),(183170048196909387/1000000000000000000),(175199685406591833/1000000000000000000)⟩
theorem valid894 : certificate894.Valid := by decide +kernel
theorem sound894 : certificate894.Sound := rat_cut_bin_certificate_sound certificate894 profilesValid894 numericValid894 valid894

def retention895 : RatCutRetentionCertificate := ⟨(99/2000),(199/4000),(8672940932256904889/19297355914231360480),(1861313903489883271/500000000000000000),(6/5),(407582406982812892174445355246193987191/372262780697976654200000000000000000000),false,MergedCutProfiles.Batch151.profile6063,(fun _ => MergedCutProfiles.Batch151.profile6063)⟩
theorem profilesValid895 : retention895.ProfilesValid := by
  exact MergedCutProfiles.Batch151.valid6063
theorem numericValid895 : retention895.NumericValid := by decide +kernel
def certificate895 : RatCutBinCertificate := ⟨⟨retention895,(1267599271441295167/500000000000000000),(29595609602345631/250000000000000000),(3302378788223152359/250000000000000000),(255273060558360408829/1000000000000000000),(266902781291072347/250000000000000000)⟩,(991220630354553697/1000000000000000000),(188928231589869211/500000000000000000),(50879115417764533/200000000000000000),(46732276871834913/250000000000000000)⟩
theorem valid895 : certificate895.Valid := by decide +kernel
theorem sound895 : certificate895.Sound := rat_cut_bin_certificate_sound certificate895 profilesValid895 numericValid895 valid895

def retention896 : RatCutRetentionCertificate := ⟨(99/2000),(199/4000),(1916064489231091151/3859471182846272096),(8672940932256904889/1000000000000000000),(21/20),(13864484580701286662277502780517746145999/13876705491611047822400000000000000000000),false,MergedCutProfiles.Batch151.profile6064,(fun _ => MergedCutProfiles.Batch151.profile6064)⟩
theorem profilesValid896 : retention896.ProfilesValid := by
  exact MergedCutProfiles.Batch151.valid6064
theorem numericValid896 : retention896.NumericValid := by decide +kernel
def certificate896 : RatCutBinCertificate := ⟨⟨retention896,(1267599271441295167/500000000000000000),(29595609602345631/250000000000000000),(3302378788223152359/250000000000000000),(255273060558360408829/1000000000000000000),(243815471090198823/250000000000000000)⟩,(991220630354553697/1000000000000000000),(206818173802782071/500000000000000000),(110608901454715843/500000000000000000),(4618404082457807/25000000000000000)⟩
theorem valid896 : certificate896.Valid := by decide +kernel
theorem sound896 : certificate896.Sound := rat_cut_bin_certificate_sound certificate896 profilesValid896 numericValid896 valid896

def retention897 : RatCutRetentionCertificate := ⟨(99/2000),(199/4000),(1/2),(1916064489231091151/200000000000000000),(21/20),(609723065345989573341765918886677140519/613140636553949168320000000000000000000),false,MergedCutProfiles.Batch151.profile6062,(fun _ => MergedCutProfiles.Batch151.profile6062)⟩
theorem profilesValid897 : retention897.ProfilesValid := by
  exact MergedCutProfiles.Batch151.valid6062
theorem numericValid897 : retention897.NumericValid := by decide +kernel
def certificate897 : RatCutBinCertificate := ⟨⟨retention897,(1267599271441295167/500000000000000000),(29595609602345631/250000000000000000),(3302378788223152359/250000000000000000),(255273060558360408829/1000000000000000000),(970568799376903221/1000000000000000000)⟩,(991220630354553697/1000000000000000000),(20781822167830923/50000000000000000),(21945706323363969/100000000000000000),(2876229581905143/15625000000000000)⟩
theorem valid897 : certificate897.Valid := by decide +kernel
theorem sound897 : certificate897.Sound := rat_cut_bin_certificate_sound certificate897 profilesValid897 numericValid897 valid897

def retention898 : RatCutRetentionCertificate := ⟨(199/4000),(1/20),(851712637786013413/19077553014247196799),(105409979924011561/125000000000000000),(29/10),(41418544868819588981/20000000000000000000),true,MergedCutProfiles.Batch151.profile6065,![MergedCutProfiles.Batch151.profile6065,MergedCutProfiles.Batch151.profile6066,MergedCutProfiles.Batch151.profile6067,MergedCutProfiles.Batch151.profile6068,MergedCutProfiles.Batch151.profile6069,MergedCutProfiles.Batch151.profile6070,MergedCutProfiles.Batch151.profile6071,MergedCutProfiles.Batch151.profile6072,MergedCutProfiles.Batch151.profile6073,MergedCutProfiles.Batch151.profile6074,MergedCutProfiles.Batch151.profile6075,MergedCutProfiles.Batch151.profile6076,MergedCutProfiles.Batch151.profile6077,MergedCutProfiles.Batch151.profile6078,MergedCutProfiles.Batch151.profile6079,MergedCutProfiles.Batch152.profile6080]⟩
theorem profilesValid898 : retention898.ProfilesValid := by
  change ∀ j : Fin 16, (retention898.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch151.valid6065
  · exact MergedCutProfiles.Batch151.valid6066
  · exact MergedCutProfiles.Batch151.valid6067
  · exact MergedCutProfiles.Batch151.valid6068
  · exact MergedCutProfiles.Batch151.valid6069
  · exact MergedCutProfiles.Batch151.valid6070
  · exact MergedCutProfiles.Batch151.valid6071
  · exact MergedCutProfiles.Batch151.valid6072
  · exact MergedCutProfiles.Batch151.valid6073
  · exact MergedCutProfiles.Batch151.valid6074
  · exact MergedCutProfiles.Batch151.valid6075
  · exact MergedCutProfiles.Batch151.valid6076
  · exact MergedCutProfiles.Batch151.valid6077
  · exact MergedCutProfiles.Batch151.valid6078
  · exact MergedCutProfiles.Batch151.valid6079
  · exact MergedCutProfiles.Batch152.valid6080
theorem numericValid898 : retention898.NumericValid := by decide +kernel
def certificate898 : RatCutBinCertificate := ⟨⟨retention898,(216391810996116503/100000000000000000),(59865971199444307/500000000000000000),(1326455612614145873/100000000000000000),(6335438781896511673/25000000000000000),(402854402276407281/200000000000000000)⟩,(992464092671492243/1000000000000000000),(372046580230009721/1000000000000000000),(130047203622133397/500000000000000000),(69718655912615789/500000000000000000)⟩
theorem valid898 : certificate898.Valid := by decide +kernel
theorem sound898 : certificate898.Sound := rat_cut_bin_certificate_sound certificate898 profilesValid898 numericValid898 valid898

def retention899 : RatCutRetentionCertificate := ⟨(199/4000),(1/20),(913151228806697765/19077553014247196799),(851712637786013413/1000000000000000000),(29/10),(2643028693430909309913/1280000000000000000000),true,MergedCutProfiles.Batch152.profile6081,![MergedCutProfiles.Batch152.profile6081,MergedCutProfiles.Batch152.profile6082,MergedCutProfiles.Batch152.profile6083,MergedCutProfiles.Batch152.profile6084,MergedCutProfiles.Batch152.profile6085,MergedCutProfiles.Batch152.profile6086,MergedCutProfiles.Batch152.profile6087,MergedCutProfiles.Batch152.profile6088,MergedCutProfiles.Batch152.profile6089,MergedCutProfiles.Batch152.profile6090,MergedCutProfiles.Batch152.profile6091,MergedCutProfiles.Batch152.profile6092,MergedCutProfiles.Batch152.profile6093,MergedCutProfiles.Batch152.profile6094,MergedCutProfiles.Batch152.profile6095,MergedCutProfiles.Batch152.profile6096]⟩
theorem profilesValid899 : retention899.ProfilesValid := by
  change ∀ j : Fin 16, (retention899.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch152.valid6081
  · exact MergedCutProfiles.Batch152.valid6082
  · exact MergedCutProfiles.Batch152.valid6083
  · exact MergedCutProfiles.Batch152.valid6084
  · exact MergedCutProfiles.Batch152.valid6085
  · exact MergedCutProfiles.Batch152.valid6086
  · exact MergedCutProfiles.Batch152.valid6087
  · exact MergedCutProfiles.Batch152.valid6088
  · exact MergedCutProfiles.Batch152.valid6089
  · exact MergedCutProfiles.Batch152.valid6090
  · exact MergedCutProfiles.Batch152.valid6091
  · exact MergedCutProfiles.Batch152.valid6092
  · exact MergedCutProfiles.Batch152.valid6093
  · exact MergedCutProfiles.Batch152.valid6094
  · exact MergedCutProfiles.Batch152.valid6095
  · exact MergedCutProfiles.Batch152.valid6096
theorem numericValid899 : retention899.NumericValid := by decide +kernel
def certificate899 : RatCutBinCertificate := ⟨⟨retention899,(216391810996116503/100000000000000000),(59865971199444307/500000000000000000),(1326455612614145873/100000000000000000),(6335438781896511673/25000000000000000),(1004105521518157363/500000000000000000)⟩,(992464092671492243/1000000000000000000),(37165640171463947/100000000000000000),(130240180134570197/500000000000000000),(69811609327054191/500000000000000000)⟩
theorem valid899 : certificate899.Valid := by decide +kernel
theorem sound899 : certificate899.Sound := rat_cut_bin_certificate_sound certificate899 profilesValid899 numericValid899 valid899

def certificates : List RatCutBinCertificate := [certificate888,certificate889,certificate890,certificate891,certificate892,certificate893,certificate894,certificate895,certificate896,certificate897,certificate898,certificate899]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound888,List.forall_mem_cons.mpr ⟨sound889,List.forall_mem_cons.mpr ⟨sound890,List.forall_mem_cons.mpr ⟨sound891,List.forall_mem_cons.mpr ⟨sound892,List.forall_mem_cons.mpr ⟨sound893,List.forall_mem_cons.mpr ⟨sound894,List.forall_mem_cons.mpr ⟨sound895,List.forall_mem_cons.mpr ⟨sound896,List.forall_mem_cons.mpr ⟨sound897,List.forall_mem_cons.mpr ⟨sound898,List.forall_mem_cons.mpr ⟨sound899,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch074
