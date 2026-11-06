import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch385
import Cycle12.MergedCutProfiles.Batch386
import Cycle12.MergedCutProfiles.Batch504
import Cycle12.MergedCutProfiles.Batch505
import Cycle12.MergedCutProfiles.Batch701
import Cycle12.MergedCutProfiles.Batch702

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch419

def retention5028 : RatCutRetentionCertificate := ⟨(53/1000),(27/500),(36308261212497890749/1598071968182840789846),(3203245673722268563/1000000000000000000),(33/20),(11441696173688189987447568208342875567399/5125193077955629700800000000000000000000),false,MergedCutProfiles.Batch701.profile28046,(fun _ => MergedCutProfiles.Batch701.profile28046)⟩
theorem profilesValid5028 : retention5028.ProfilesValid := by
  exact MergedCutProfiles.Batch701.valid28046
theorem numericValid5028 : retention5028.NumericValid := by decide +kernel
def certificate5028 : RatCutBinCertificate := ⟨⟨retention5028,(963364464023034543/500000000000000000),(142705547327693923/1000000000000000000),(14016825076817498371/1000000000000000000),(5632878126100667510879/250000000000000000),(2200075437544352449/1000000000000000000)⟩,(12499077214500187/12500000000000000),(720792960303760693/1000000000000000000),(43217017590298659/1000000000000000000),(46012122649057033/1000000000000000000)⟩
theorem valid5028 : certificate5028.Valid := by decide +kernel
theorem sound5028 : certificate5028.Sound := rat_cut_bin_certificate_sound certificate5028 profilesValid5028 numericValid5028 valid5028

def retention5029 : RatCutRetentionCertificate := ⟨(53/1000),(27/500),(1/40),(36308261212497890749/1000000000000000000),(21/20),(128961572814953836605507799535521354157679/58093217939996625198400000000000000000000),false,MergedCutProfiles.Batch701.profile28047,(fun _ => MergedCutProfiles.Batch701.profile28047)⟩
theorem profilesValid5029 : retention5029.ProfilesValid := by
  exact MergedCutProfiles.Batch701.valid28047
theorem numericValid5029 : retention5029.NumericValid := by decide +kernel
def certificate5029 : RatCutBinCertificate := ⟨⟨retention5029,(963364464023034543/500000000000000000),(142705547327693923/1000000000000000000),(14016825076817498371/1000000000000000000),(5632878126100667510879/250000000000000000),(219931067668386753/100000000000000000)⟩,(12499077214500187/12500000000000000),(170065074049206439/250000000000000000),(14412294091015767/250000000000000000),(114453558023756669/1000000000000000000)⟩
theorem valid5029 : certificate5029.Valid := by decide +kernel
theorem sound5029 : certificate5029.Sound := rat_cut_bin_certificate_sound certificate5029 profilesValid5029 numericValid5029 valid5029

def retention5030 : RatCutRetentionCertificate := ⟨(27/500),(11/200),(621121845046980005/1531430777779363765248),(152220822724973043/250000000000000000),4,(38910433980888024706119282747333551/16913424747219227000000000000000000),true,MergedCutProfiles.Batch701.profile28048,![MergedCutProfiles.Batch701.profile28048,MergedCutProfiles.Batch701.profile28049,MergedCutProfiles.Batch701.profile28050,MergedCutProfiles.Batch701.profile28051,MergedCutProfiles.Batch701.profile28052,MergedCutProfiles.Batch701.profile28053,MergedCutProfiles.Batch701.profile28054,MergedCutProfiles.Batch701.profile28055,MergedCutProfiles.Batch701.profile28056,MergedCutProfiles.Batch701.profile28057,MergedCutProfiles.Batch701.profile28058,MergedCutProfiles.Batch701.profile28059,MergedCutProfiles.Batch701.profile28060,MergedCutProfiles.Batch701.profile28061,MergedCutProfiles.Batch701.profile28062,MergedCutProfiles.Batch701.profile28063]⟩
theorem profilesValid5030 : retention5030.ProfilesValid := by
  change ∀ j : Fin 16, (retention5030.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch701.valid28048
  · exact MergedCutProfiles.Batch701.valid28049
  · exact MergedCutProfiles.Batch701.valid28050
  · exact MergedCutProfiles.Batch701.valid28051
  · exact MergedCutProfiles.Batch701.valid28052
  · exact MergedCutProfiles.Batch701.valid28053
  · exact MergedCutProfiles.Batch701.valid28054
  · exact MergedCutProfiles.Batch701.valid28055
  · exact MergedCutProfiles.Batch701.valid28056
  · exact MergedCutProfiles.Batch701.valid28057
  · exact MergedCutProfiles.Batch701.valid28058
  · exact MergedCutProfiles.Batch701.valid28059
  · exact MergedCutProfiles.Batch701.valid28060
  · exact MergedCutProfiles.Batch701.valid28061
  · exact MergedCutProfiles.Batch701.valid28062
  · exact MergedCutProfiles.Batch701.valid28063
theorem numericValid5030 : retention5030.NumericValid := by decide +kernel
def certificate5030 : RatCutBinCertificate := ⟨⟨retention5030,(1937032247133863393/1000000000000000000),(14887102204219317/100000000000000000),(7130251994533149149/500000000000000000),(2196814309103604449509/100000000000000000),(1109839530110671133/500000000000000000)⟩,(3905954716610639/3906250000000000),(348398233046456823/500000000000000000),(51477501169652663/1000000000000000000),(581573099655513/25000000000000000)⟩
theorem valid5030 : certificate5030.Valid := by decide +kernel
theorem sound5030 : certificate5030.Sound := rat_cut_bin_certificate_sound certificate5030 profilesValid5030 numericValid5030 valid5030

def retention5031 : RatCutRetentionCertificate := ⟨(27/500),(11/200),(2147736693359375/2991075737850319854),(124224369009396001/200000000000000000),4,(1439372118466837038176594631801720891/621121845046980005000000000000000000),true,MergedCutProfiles.Batch701.profile28064,![MergedCutProfiles.Batch701.profile28064,MergedCutProfiles.Batch701.profile28065,MergedCutProfiles.Batch701.profile28052,MergedCutProfiles.Batch701.profile28054,MergedCutProfiles.Batch701.profile28056,MergedCutProfiles.Batch701.profile28066,MergedCutProfiles.Batch701.profile28067,MergedCutProfiles.Batch701.profile28061,MergedCutProfiles.Batch701.profile28063,MergedCutProfiles.Batch701.profile28068,MergedCutProfiles.Batch701.profile28069,MergedCutProfiles.Batch701.profile28070,MergedCutProfiles.Batch701.profile28071,MergedCutProfiles.Batch701.profile28072,MergedCutProfiles.Batch504.profile20190,MergedCutProfiles.Batch701.profile28073]⟩
theorem profilesValid5031 : retention5031.ProfilesValid := by
  change ∀ j : Fin 16, (retention5031.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch701.valid28064
  · exact MergedCutProfiles.Batch701.valid28065
  · exact MergedCutProfiles.Batch701.valid28052
  · exact MergedCutProfiles.Batch701.valid28054
  · exact MergedCutProfiles.Batch701.valid28056
  · exact MergedCutProfiles.Batch701.valid28066
  · exact MergedCutProfiles.Batch701.valid28067
  · exact MergedCutProfiles.Batch701.valid28061
  · exact MergedCutProfiles.Batch701.valid28063
  · exact MergedCutProfiles.Batch701.valid28068
  · exact MergedCutProfiles.Batch701.valid28069
  · exact MergedCutProfiles.Batch701.valid28070
  · exact MergedCutProfiles.Batch701.valid28071
  · exact MergedCutProfiles.Batch701.valid28072
  · exact MergedCutProfiles.Batch504.valid20190
  · exact MergedCutProfiles.Batch701.valid28073
theorem numericValid5031 : retention5031.NumericValid := by decide +kernel
def certificate5031 : RatCutBinCertificate := ⟨⟨retention5031,(1937032247133863393/1000000000000000000),(14887102204219317/100000000000000000),(7130251994533149149/500000000000000000),(2196814309103604449509/100000000000000000),(2236488818184202617/1000000000000000000)⟩,(3905954716610639/3906250000000000),(682643458458340347/1000000000000000000),(14183790445033673/250000000000000000),(12946029740930887/500000000000000000)⟩
theorem valid5031 : certificate5031.Valid := by decide +kernel
theorem sound5031 : certificate5031.Sound := rat_cut_bin_certificate_sound certificate5031 profilesValid5031 numericValid5031 valid5031

def retention5032 : RatCutRetentionCertificate := ⟨(27/500),(11/200),(465515448183693797/191428847222420470656),(1099641187/1000000000),(29/10),(3826507078891233421/1600000000000000000),true,MergedCutProfiles.Batch701.profile28053,![MergedCutProfiles.Batch701.profile28053,MergedCutProfiles.Batch701.profile28059,MergedCutProfiles.Batch701.profile28068,MergedCutProfiles.Batch701.profile28074,MergedCutProfiles.Batch701.profile28075,MergedCutProfiles.Batch505.profile20216,MergedCutProfiles.Batch701.profile28076,MergedCutProfiles.Batch505.profile20224,MergedCutProfiles.Batch504.profile20191,MergedCutProfiles.Batch701.profile28077,MergedCutProfiles.Batch505.profile20205,MergedCutProfiles.Batch701.profile28078,MergedCutProfiles.Batch385.profile15408,MergedCutProfiles.Batch701.profile28079,MergedCutProfiles.Batch702.profile28080,MergedCutProfiles.Batch702.profile28081]⟩
theorem profilesValid5032 : retention5032.ProfilesValid := by
  change ∀ j : Fin 16, (retention5032.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch701.valid28053
  · exact MergedCutProfiles.Batch701.valid28059
  · exact MergedCutProfiles.Batch701.valid28068
  · exact MergedCutProfiles.Batch701.valid28074
  · exact MergedCutProfiles.Batch701.valid28075
  · exact MergedCutProfiles.Batch505.valid20216
  · exact MergedCutProfiles.Batch701.valid28076
  · exact MergedCutProfiles.Batch505.valid20224
  · exact MergedCutProfiles.Batch504.valid20191
  · exact MergedCutProfiles.Batch701.valid28077
  · exact MergedCutProfiles.Batch505.valid20205
  · exact MergedCutProfiles.Batch701.valid28078
  · exact MergedCutProfiles.Batch385.valid15408
  · exact MergedCutProfiles.Batch701.valid28079
  · exact MergedCutProfiles.Batch702.valid28080
  · exact MergedCutProfiles.Batch702.valid28081
theorem numericValid5032 : retention5032.NumericValid := by decide +kernel
def certificate5032 : RatCutBinCertificate := ⟨⟨retention5032,(1937032247133863393/1000000000000000000),(14887102204219317/100000000000000000),(7130251994533149149/500000000000000000),(2196814309103604449509/100000000000000000),(466584922925027477/200000000000000000)⟩,(3905954716610639/3906250000000000),(469379725923240661/1000000000000000000),(175607969254723811/1000000000000000000),(112800968772907497/1000000000000000000)⟩
theorem valid5032 : certificate5032.Valid := by decide +kernel
theorem sound5032 : certificate5032.Sound := rat_cut_bin_certificate_sound certificate5032 profilesValid5032 numericValid5032 valid5032

def retention5033 : RatCutRetentionCertificate := ⟨(27/500),(11/200),(62500000000000000/1495537868925159927),(465515448183693797/125000000000000000),(27/20),(336070952314111554651/160000000000000000000),true,MergedCutProfiles.Batch702.profile28082,![MergedCutProfiles.Batch702.profile28082,MergedCutProfiles.Batch702.profile28083,MergedCutProfiles.Batch702.profile28084,MergedCutProfiles.Batch702.profile28085,MergedCutProfiles.Batch702.profile28086,MergedCutProfiles.Batch702.profile28087,MergedCutProfiles.Batch702.profile28088,MergedCutProfiles.Batch702.profile28089,MergedCutProfiles.Batch702.profile28090,MergedCutProfiles.Batch702.profile28091,MergedCutProfiles.Batch385.profile15407,MergedCutProfiles.Batch702.profile28092,MergedCutProfiles.Batch702.profile28093,MergedCutProfiles.Batch702.profile28094,MergedCutProfiles.Batch702.profile28095,MergedCutProfiles.Batch702.profile28096]⟩
theorem profilesValid5033 : retention5033.ProfilesValid := by
  change ∀ j : Fin 16, (retention5033.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch702.valid28082
  · exact MergedCutProfiles.Batch702.valid28083
  · exact MergedCutProfiles.Batch702.valid28084
  · exact MergedCutProfiles.Batch702.valid28085
  · exact MergedCutProfiles.Batch702.valid28086
  · exact MergedCutProfiles.Batch702.valid28087
  · exact MergedCutProfiles.Batch702.valid28088
  · exact MergedCutProfiles.Batch702.valid28089
  · exact MergedCutProfiles.Batch702.valid28090
  · exact MergedCutProfiles.Batch702.valid28091
  · exact MergedCutProfiles.Batch385.valid15407
  · exact MergedCutProfiles.Batch702.valid28092
  · exact MergedCutProfiles.Batch702.valid28093
  · exact MergedCutProfiles.Batch702.valid28094
  · exact MergedCutProfiles.Batch702.valid28095
  · exact MergedCutProfiles.Batch702.valid28096
theorem numericValid5033 : retention5033.NumericValid := by decide +kernel
def certificate5033 : RatCutBinCertificate := ⟨⟨retention5033,(1937032247133863393/1000000000000000000),(14887102204219317/100000000000000000),(7130251994533149149/500000000000000000),(2196814309103604449509/100000000000000000),(25914305836838327/12500000000000000)⟩,(3905954716610639/3906250000000000),(337717788658794849/1000000000000000000),(295666253307401337/1000000000000000000),(173888770902585999/500000000000000000)⟩
theorem valid5033 : certificate5033.Valid := by decide +kernel
theorem sound5033 : certificate5033.Sound := rat_cut_bin_certificate_sound certificate5033 profilesValid5033 numericValid5033 valid5033

def retention5034 : RatCutRetentionCertificate := ⟨(27/500),(11/200),(1/2),64,1,(10215983555265238754732139412177955919/10240000000000000000000000000000000000),false,MergedCutProfiles.Batch386.profile15456,(fun _ => MergedCutProfiles.Batch386.profile15456)⟩
theorem profilesValid5034 : retention5034.ProfilesValid := by
  exact MergedCutProfiles.Batch386.valid15456
theorem numericValid5034 : retention5034.NumericValid := by decide +kernel
def certificate5034 : RatCutBinCertificate := ⟨⟨retention5034,(1937032247133863393/1000000000000000000),(14887102204219317/100000000000000000),(7130251994533149149/500000000000000000),(2196814309103604449509/100000000000000000),(977433198801956751/1000000000000000000)⟩,(3905954716610639/3906250000000000),(556876228322118167/1000000000000000000),(2342431719924591/20000000000000000),(56373925507683131/500000000000000000)⟩
theorem valid5034 : certificate5034.Valid := by decide +kernel
theorem sound5034 : certificate5034.Sound := rat_cut_bin_certificate_sound certificate5034 profilesValid5034 numericValid5034 valid5034

def retention5035 : RatCutRetentionCertificate := ⟨(27/500),(11/200),(62500000000000000/1495537868925159927),(40641669653263970401/1000000000000000000),1,(536020511964558280522596381521081169/254010435332899815006250000000000000),false,MergedCutProfiles.Batch702.profile28097,(fun _ => MergedCutProfiles.Batch702.profile28097)⟩
theorem profilesValid5035 : retention5035.ProfilesValid := by
  exact MergedCutProfiles.Batch702.valid28097
theorem numericValid5035 : retention5035.NumericValid := by decide +kernel
def certificate5035 : RatCutBinCertificate := ⟨⟨retention5035,(1734041204133863393/1000000000000000000),(14887102204219317/100000000000000000),(7130251994533149149/500000000000000000),(2196814309103604449509/100000000000000000),(1046063968463867511/500000000000000000)⟩,(499966164626391481/500000000000000000),(8587468509604537/500000000000000000),(441318252544053693/500000000000000000),(1756063659668924859/1000000000000000000)⟩
theorem valid5035 : certificate5035.Valid := by decide +kernel
theorem sound5035 : certificate5035.Sound := rat_cut_bin_certificate_sound certificate5035 profilesValid5035 numericValid5035 valid5035

def retention5036 : RatCutRetentionCertificate := ⟨(27/500),(11/200),(1/2),64,1,(10215983555265238754732139412177955919/10240000000000000000000000000000000000),false,MergedCutProfiles.Batch386.profile15456,(fun _ => MergedCutProfiles.Batch386.profile15456)⟩
theorem profilesValid5036 : retention5036.ProfilesValid := by
  exact MergedCutProfiles.Batch386.valid15456
theorem numericValid5036 : retention5036.NumericValid := by decide +kernel
def certificate5036 : RatCutBinCertificate := ⟨⟨retention5036,(1734041204133863393/1000000000000000000),(14887102204219317/100000000000000000),(7130251994533149149/500000000000000000),(2196814309103604449509/100000000000000000),(195910460506976439/200000000000000000)⟩,(499966164626391481/500000000000000000),(9170558187622173/250000000000000000),(825072416527220309/1000000000000000000),(49747726149002937/62500000000000000)⟩
theorem valid5036 : certificate5036.Valid := by decide +kernel
theorem sound5036 : certificate5036.Sound := rat_cut_bin_certificate_sound certificate5036 profilesValid5036 numericValid5036 valid5036

def retention5037 : RatCutRetentionCertificate := ⟨(27/500),(11/200),(738650397365141591/1531430777779363765248),(146267405418839919/200000000000000000),4,(55646670670188781914375490998675727/22854282096693737343750000000000000),false,MergedCutProfiles.Batch702.profile28098,(fun _ => MergedCutProfiles.Batch702.profile28098)⟩
theorem profilesValid5037 : retention5037.ProfilesValid := by
  exact MergedCutProfiles.Batch702.valid28098
theorem numericValid5037 : retention5037.NumericValid := by decide +kernel
def certificate5037 : RatCutBinCertificate := ⟨⟨retention5037,(1935182033133863393/1000000000000000000),(14887102204219317/100000000000000000),(7130251994533149149/500000000000000000),(2196814309103604449509/100000000000000000),(2354037883759905063/1000000000000000000)⟩,(999924479657702943/1000000000000000000),(810611883894910717/1000000000000000000),(3837451776609901/200000000000000000),(9399841413773511/1000000000000000000)⟩
theorem valid5037 : certificate5037.Valid := by decide +kernel
theorem sound5037 : certificate5037.Sound := rat_cut_bin_certificate_sound certificate5037 profilesValid5037 numericValid5037 valid5037

def retention5038 : RatCutRetentionCertificate := ⟨(27/500),(11/200),(874786938834916879/1531430777779363765248),(738650397365141591/1000000000000000000),4,(11246552525866600652815456667110821/4616564983532134943750000000000000),false,MergedCutProfiles.Batch702.profile28099,(fun _ => MergedCutProfiles.Batch702.profile28099)⟩
theorem profilesValid5038 : retention5038.ProfilesValid := by
  exact MergedCutProfiles.Batch702.valid28099
theorem numericValid5038 : retention5038.NumericValid := by decide +kernel
def certificate5038 : RatCutBinCertificate := ⟨⟨retention5038,(1935182033133863393/1000000000000000000),(14887102204219317/100000000000000000),(7130251994533149149/500000000000000000),(2196814309103604449509/100000000000000000),(1177660659159581307/500000000000000000)⟩,(999924479657702943/1000000000000000000),(404190436611302357/500000000000000000),(19658768032041053/1000000000000000000),(9651217312447561/1000000000000000000)⟩
theorem valid5038 : certificate5038.Valid := by decide +kernel
theorem sound5038 : certificate5038.Sound := rat_cut_bin_certificate_sound certificate5038 profilesValid5038 numericValid5038 valid5038

def retention5039 : RatCutRetentionCertificate := ⟨(27/500),(11/200),(394702176359188673/191428847222420470656),(874786938834916879/1000000000000000000),(73/20),(3382047478543505255390016353782837663831/1399659102135867006400000000000000000000),false,MergedCutProfiles.Batch702.profile28100,(fun _ => MergedCutProfiles.Batch702.profile28100)⟩
theorem profilesValid5039 : retention5039.ProfilesValid := by
  exact MergedCutProfiles.Batch702.valid28100
theorem numericValid5039 : retention5039.NumericValid := by decide +kernel
def certificate5039 : RatCutBinCertificate := ⟨⟨retention5039,(1935182033133863393/1000000000000000000),(14887102204219317/100000000000000000),(7130251994533149149/500000000000000000),(2196814309103604449509/100000000000000000),(2342598649484049757/1000000000000000000)⟩,(999924479657702943/1000000000000000000),(392387203998483679/500000000000000000),(12514233142397353/500000000000000000),(13373812190087977/1000000000000000000)⟩
theorem valid5039 : certificate5039.Valid := by decide +kernel
theorem sound5039 : certificate5039.Sound := rat_cut_bin_certificate_sound certificate5039 profilesValid5039 numericValid5039 valid5039

def certificates : List RatCutBinCertificate := [certificate5028,certificate5029,certificate5030,certificate5031,certificate5032,certificate5033,certificate5034,certificate5035,certificate5036,certificate5037,certificate5038,certificate5039]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound5028,List.forall_mem_cons.mpr ⟨sound5029,List.forall_mem_cons.mpr ⟨sound5030,List.forall_mem_cons.mpr ⟨sound5031,List.forall_mem_cons.mpr ⟨sound5032,List.forall_mem_cons.mpr ⟨sound5033,List.forall_mem_cons.mpr ⟨sound5034,List.forall_mem_cons.mpr ⟨sound5035,List.forall_mem_cons.mpr ⟨sound5036,List.forall_mem_cons.mpr ⟨sound5037,List.forall_mem_cons.mpr ⟨sound5038,List.forall_mem_cons.mpr ⟨sound5039,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch419
