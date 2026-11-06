import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch125
import Cycle12.MergedCutProfiles.Batch126
import Cycle12.MergedCutProfiles.Batch127

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch062

def retention744 : RatCutRetentionCertificate := ⟨(93/2000),(187/4000),(1224882245285263935/2469771234719057963),(10180423827336650047/1000000000000000000),(21/20),(16345689530328338506124552439331936221911/16288678123738640075200000000000000000000),false,MergedCutProfiles.Batch125.profile5013,(fun _ => MergedCutProfiles.Batch125.profile5013)⟩
theorem profilesValid744 : retention744.ProfilesValid := by
  exact MergedCutProfiles.Batch125.valid5013
theorem numericValid744 : retention744.NumericValid := by decide +kernel
def certificate744 : RatCutBinCertificate := ⟨⟨retention744,(426411054045357163/200000000000000000),(102941493058315297/1000000000000000000),(2515075777424674363/200000000000000000),(279916723399605254071/1000000000000000000),(49258693886033943/50000000000000000)⟩,(99315256850220439/100000000000000000),(242403902729813999/500000000000000000),(82094963313549873/500000000000000000),(17575558667844013/125000000000000000)⟩
theorem valid744 : certificate744.Valid := by decide +kernel
theorem sound744 : certificate744.Sound := rat_cut_bin_certificate_sound certificate744 profilesValid744 numericValid744 valid744

def retention745 : RatCutRetentionCertificate := ⟨(93/2000),(187/4000),(1/2),(2204788041513475083/200000000000000000),(21/20),(703372248088938896180182489492132219031/705532173284312026560000000000000000000),false,MergedCutProfiles.Batch125.profile5014,(fun _ => MergedCutProfiles.Batch125.profile5014)⟩
theorem profilesValid745 : retention745.ProfilesValid := by
  exact MergedCutProfiles.Batch125.valid5014
theorem numericValid745 : retention745.NumericValid := by decide +kernel
def certificate745 : RatCutBinCertificate := ⟨⟨retention745,(426411054045357163/200000000000000000),(102941493058315297/1000000000000000000),(2515075777424674363/200000000000000000),(279916723399605254071/1000000000000000000),(489306224888889819/500000000000000000)⟩,(99315256850220439/100000000000000000),(777543497242351/1600000000000000),(81676862360421231/500000000000000000),(34973301027976297/250000000000000000)⟩
theorem valid745 : certificate745.Valid := by decide +kernel
theorem sound745 : certificate745.Sound := rat_cut_bin_certificate_sound certificate745 profilesValid745 numericValid745 valid745

def retention746 : RatCutRetentionCertificate := ⟨(93/2000),(187/4000),(3298301662135562585/7409313704157173889),(746357658101164341/200000000000000000),(6/5),(228723194274990816072624585007707423/207321571694767872500000000000000000),false,MergedCutProfiles.Batch125.profile5015,(fun _ => MergedCutProfiles.Batch125.profile5015)⟩
theorem profilesValid746 : retention746.ProfilesValid := by
  exact MergedCutProfiles.Batch125.valid5015
theorem numericValid746 : retention746.NumericValid := by decide +kernel
def certificate746 : RatCutBinCertificate := ⟨⟨retention746,(501538435845357163/200000000000000000),(102941493058315297/1000000000000000000),(2515075777424674363/200000000000000000),(279916723399605254071/1000000000000000000),(539296832450514561/500000000000000000)⟩,(495972525602252361/500000000000000000),(375754719837954523/1000000000000000000),(64111692563736159/250000000000000000),(7611342943279353/40000000000000000)⟩
theorem valid746 : certificate746.Valid := by decide +kernel
theorem sound746 : certificate746.Sound := rat_cut_bin_certificate_sound certificate746 profilesValid746 numericValid746 valid746

def retention747 : RatCutRetentionCertificate := ⟨(93/2000),(187/4000),(11039432286594745916/22227941112471521667),(1978980997281337551/200000000000000000),(21/20),(211428031303121924173648617526365043557/211091306376676005440000000000000000000),false,MergedCutProfiles.Batch125.profile5016,(fun _ => MergedCutProfiles.Batch125.profile5016)⟩
theorem profilesValid747 : retention747.ProfilesValid := by
  exact MergedCutProfiles.Batch125.valid5016
theorem numericValid747 : retention747.NumericValid := by decide +kernel
def certificate747 : RatCutBinCertificate := ⟨⟨retention747,(501538435845357163/200000000000000000),(102941493058315297/1000000000000000000),(2515075777424674363/200000000000000000),(279916723399605254071/1000000000000000000),(245010037466018857/250000000000000000)⟩,(495972525602252361/500000000000000000),(413540874248967419/1000000000000000000),(110651046071865179/500000000000000000),(37587554331006431/200000000000000000)⟩
theorem valid747 : certificate747.Valid := by decide +kernel
theorem sound747 : certificate747.Sound := rat_cut_bin_certificate_sound certificate747 profilesValid747 numericValid747 valid747

def retention748 : RatCutRetentionCertificate := ⟨(93/2000),(187/4000),(1/2),(2759858071648686479/250000000000000000),(21/20),(1100588154739362284145770751176200487759/1103943228659474591600000000000000000000),false,MergedCutProfiles.Batch125.profile5014,(fun _ => MergedCutProfiles.Batch125.profile5014)⟩
theorem profilesValid748 : retention748.ProfilesValid := by
  exact MergedCutProfiles.Batch125.valid5014
theorem numericValid748 : retention748.NumericValid := by decide +kernel
def certificate748 : RatCutBinCertificate := ⟨⟨retention748,(501538435845357163/200000000000000000),(102941493058315297/1000000000000000000),(2515075777424674363/200000000000000000),(279916723399605254071/1000000000000000000),(195081178798485763/200000000000000000)⟩,(495972525602252361/500000000000000000),(103876412596555591/250000000000000000),(109785954690625003/500000000000000000),(187258683951210811/1000000000000000000)⟩
theorem valid748 : certificate748.Valid := by decide +kernel
theorem sound748 : certificate748.Sound := rat_cut_bin_certificate_sound certificate748 profilesValid748 numericValid748 valid748

def retention749 : RatCutRetentionCertificate := ⟨(187/4000),(47/1000),(837480314452227533/21961260129902898230),(829188430150720329/1000000000000000000),3,(537756709949668803777/256000000000000000000),true,MergedCutProfiles.Batch125.profile5017,![MergedCutProfiles.Batch125.profile5017,MergedCutProfiles.Batch125.profile5018,MergedCutProfiles.Batch125.profile5019,MergedCutProfiles.Batch125.profile5020,MergedCutProfiles.Batch125.profile5021,MergedCutProfiles.Batch125.profile5022,MergedCutProfiles.Batch125.profile5023,MergedCutProfiles.Batch125.profile5024,MergedCutProfiles.Batch125.profile5025,MergedCutProfiles.Batch125.profile5026,MergedCutProfiles.Batch125.profile5027,MergedCutProfiles.Batch125.profile5028,MergedCutProfiles.Batch125.profile5029,MergedCutProfiles.Batch125.profile5030,MergedCutProfiles.Batch125.profile5031,MergedCutProfiles.Batch125.profile5032]⟩
theorem profilesValid749 : retention749.ProfilesValid := by
  change ∀ j : Fin 16, (retention749.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch125.valid5017
  · exact MergedCutProfiles.Batch125.valid5018
  · exact MergedCutProfiles.Batch125.valid5019
  · exact MergedCutProfiles.Batch125.valid5020
  · exact MergedCutProfiles.Batch125.valid5021
  · exact MergedCutProfiles.Batch125.valid5022
  · exact MergedCutProfiles.Batch125.valid5023
  · exact MergedCutProfiles.Batch125.valid5024
  · exact MergedCutProfiles.Batch125.valid5025
  · exact MergedCutProfiles.Batch125.valid5026
  · exact MergedCutProfiles.Batch125.valid5027
  · exact MergedCutProfiles.Batch125.valid5028
  · exact MergedCutProfiles.Batch125.valid5029
  · exact MergedCutProfiles.Batch125.valid5030
  · exact MergedCutProfiles.Batch125.valid5031
  · exact MergedCutProfiles.Batch125.valid5032
theorem numericValid749 : retention749.NumericValid := by decide +kernel
def certificate749 : RatCutBinCertificate := ⟨⟨retention749,(1067127128350819737/500000000000000000),(6511012982960937/62500000000000000),(12626426173190284547/1000000000000000000),(277681659324691596311/1000000000000000000),(511944308562862587/250000000000000000)⟩,(993099642606045611/1000000000000000000),(15209732578942419/40000000000000000),(50416059028902367/200000000000000000),(133918005432567347/1000000000000000000)⟩
theorem valid749 : certificate749.Valid := by decide +kernel
theorem sound749 : certificate749.Sound := rat_cut_bin_certificate_sound certificate749 profilesValid749 numericValid749 valid749

def retention750 : RatCutRetentionCertificate := ⟨(187/4000),(47/1000),(87092592700000000/2196126012990289823),(837480314452227533/1000000000000000000),3,(107469846409995092641/51200000000000000000),true,MergedCutProfiles.Batch125.profile5033,![MergedCutProfiles.Batch125.profile5033,MergedCutProfiles.Batch125.profile5034,MergedCutProfiles.Batch125.profile5035,MergedCutProfiles.Batch125.profile5036,MergedCutProfiles.Batch125.profile5037,MergedCutProfiles.Batch125.profile5038,MergedCutProfiles.Batch125.profile5039,MergedCutProfiles.Batch126.profile5040,MergedCutProfiles.Batch126.profile5041,MergedCutProfiles.Batch126.profile5042,MergedCutProfiles.Batch126.profile5043,MergedCutProfiles.Batch126.profile5044,MergedCutProfiles.Batch126.profile5045,MergedCutProfiles.Batch126.profile5046,MergedCutProfiles.Batch126.profile5047,MergedCutProfiles.Batch126.profile5048]⟩
theorem profilesValid750 : retention750.ProfilesValid := by
  change ∀ j : Fin 16, (retention750.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch125.valid5033
  · exact MergedCutProfiles.Batch125.valid5034
  · exact MergedCutProfiles.Batch125.valid5035
  · exact MergedCutProfiles.Batch125.valid5036
  · exact MergedCutProfiles.Batch125.valid5037
  · exact MergedCutProfiles.Batch125.valid5038
  · exact MergedCutProfiles.Batch125.valid5039
  · exact MergedCutProfiles.Batch126.valid5040
  · exact MergedCutProfiles.Batch126.valid5041
  · exact MergedCutProfiles.Batch126.valid5042
  · exact MergedCutProfiles.Batch126.valid5043
  · exact MergedCutProfiles.Batch126.valid5044
  · exact MergedCutProfiles.Batch126.valid5045
  · exact MergedCutProfiles.Batch126.valid5046
  · exact MergedCutProfiles.Batch126.valid5047
  · exact MergedCutProfiles.Batch126.valid5048
theorem numericValid750 : retention750.NumericValid := by decide +kernel
def certificate750 : RatCutBinCertificate := ⟨⟨retention750,(1067127128350819737/500000000000000000),(6511012982960937/62500000000000000),(12626426173190284547/1000000000000000000),(277681659324691596311/1000000000000000000),(2046185602588333373/1000000000000000000)⟩,(993099642606045611/1000000000000000000),(378950105794417419/1000000000000000000),(126666431438494059/500000000000000000),(67394904415687497/500000000000000000)⟩
theorem valid750 : certificate750.Valid := by decide +kernel
theorem sound750 : certificate750.Sound := rat_cut_bin_certificate_sound certificate750 profilesValid750 numericValid750 valid750

def retention751 : RatCutRetentionCertificate := ⟨(187/4000),(47/1000),(953130718373238403/21961260129902898230),(870925927/1000000000),(57/20),(33205755804260481711/16000000000000000000),true,MergedCutProfiles.Batch126.profile5049,![MergedCutProfiles.Batch126.profile5049,MergedCutProfiles.Batch126.profile5050,MergedCutProfiles.Batch126.profile5051,MergedCutProfiles.Batch126.profile5052,MergedCutProfiles.Batch126.profile5053,MergedCutProfiles.Batch126.profile5054,MergedCutProfiles.Batch125.profile5024,MergedCutProfiles.Batch126.profile5055,MergedCutProfiles.Batch126.profile5056,MergedCutProfiles.Batch126.profile5057,MergedCutProfiles.Batch126.profile5044,MergedCutProfiles.Batch126.profile5058,MergedCutProfiles.Batch126.profile5059,MergedCutProfiles.Batch125.profile5032,MergedCutProfiles.Batch126.profile5060,MergedCutProfiles.Batch126.profile5061]⟩
theorem profilesValid751 : retention751.ProfilesValid := by
  change ∀ j : Fin 16, (retention751.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch126.valid5049
  · exact MergedCutProfiles.Batch126.valid5050
  · exact MergedCutProfiles.Batch126.valid5051
  · exact MergedCutProfiles.Batch126.valid5052
  · exact MergedCutProfiles.Batch126.valid5053
  · exact MergedCutProfiles.Batch126.valid5054
  · exact MergedCutProfiles.Batch125.valid5024
  · exact MergedCutProfiles.Batch126.valid5055
  · exact MergedCutProfiles.Batch126.valid5056
  · exact MergedCutProfiles.Batch126.valid5057
  · exact MergedCutProfiles.Batch126.valid5044
  · exact MergedCutProfiles.Batch126.valid5058
  · exact MergedCutProfiles.Batch126.valid5059
  · exact MergedCutProfiles.Batch125.valid5032
  · exact MergedCutProfiles.Batch126.valid5060
  · exact MergedCutProfiles.Batch126.valid5061
theorem numericValid751 : retention751.NumericValid := by decide +kernel
def certificate751 : RatCutBinCertificate := ⟨⟨retention751,(1067127128350819737/500000000000000000),(6511012982960937/62500000000000000),(12626426173190284547/1000000000000000000),(277681659324691596311/1000000000000000000),(2025166552929601699/1000000000000000000)⟩,(993099642606045611/1000000000000000000),(188358900361952567/500000000000000000),(255505398888487211/1000000000000000000),(35000124788424219/250000000000000000)⟩
theorem valid751 : certificate751.Valid := by decide +kernel
theorem sound751 : certificate751.Sound := rat_cut_bin_certificate_sound certificate751 profilesValid751 numericValid751 valid751

def retention752 : RatCutRetentionCertificate := ⟨(187/4000),(47/1000),(1663984967123739929/21961260129902898230),(953130718373238403/1000000000000000000),(53/20),(631298756069137658773/320000000000000000000),true,MergedCutProfiles.Batch126.profile5062,![MergedCutProfiles.Batch126.profile5062,MergedCutProfiles.Batch125.profile5020,MergedCutProfiles.Batch125.profile5022,MergedCutProfiles.Batch126.profile5063,MergedCutProfiles.Batch126.profile5064,MergedCutProfiles.Batch126.profile5065,MergedCutProfiles.Batch126.profile5066,MergedCutProfiles.Batch126.profile5067,MergedCutProfiles.Batch126.profile5068,MergedCutProfiles.Batch126.profile5069,MergedCutProfiles.Batch126.profile5070,MergedCutProfiles.Batch126.profile5071,MergedCutProfiles.Batch126.profile5072,MergedCutProfiles.Batch126.profile5073,MergedCutProfiles.Batch126.profile5074,MergedCutProfiles.Batch126.profile5075]⟩
theorem profilesValid752 : retention752.ProfilesValid := by
  change ∀ j : Fin 16, (retention752.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch126.valid5062
  · exact MergedCutProfiles.Batch125.valid5020
  · exact MergedCutProfiles.Batch125.valid5022
  · exact MergedCutProfiles.Batch126.valid5063
  · exact MergedCutProfiles.Batch126.valid5064
  · exact MergedCutProfiles.Batch126.valid5065
  · exact MergedCutProfiles.Batch126.valid5066
  · exact MergedCutProfiles.Batch126.valid5067
  · exact MergedCutProfiles.Batch126.valid5068
  · exact MergedCutProfiles.Batch126.valid5069
  · exact MergedCutProfiles.Batch126.valid5070
  · exact MergedCutProfiles.Batch126.valid5071
  · exact MergedCutProfiles.Batch126.valid5072
  · exact MergedCutProfiles.Batch126.valid5073
  · exact MergedCutProfiles.Batch126.valid5074
  · exact MergedCutProfiles.Batch126.valid5075
theorem numericValid752 : retention752.NumericValid := by decide +kernel
def certificate752 : RatCutBinCertificate := ⟨⟨retention752,(1067127128350819737/500000000000000000),(6511012982960937/62500000000000000),(12626426173190284547/1000000000000000000),(277681659324691596311/1000000000000000000),(481534469637230249/250000000000000000)⟩,(993099642606045611/1000000000000000000),(95521612877342371/250000000000000000),(62575668314899321/250000000000000000),(70064510850699059/500000000000000000)⟩
theorem valid752 : certificate752.Valid := by decide +kernel
theorem sound752 : certificate752.Sound := rat_cut_bin_certificate_sound certificate752 profilesValid752 numericValid752 valid752

def retention753 : RatCutRetentionCertificate := ⟨(187/4000),(47/1000),(565820103365832283/2196126012990289823),(1663984967123739929/1000000000000000000),(7/4),(159852018457312739724910487070973358991/106495037895919355456000000000000000000),false,MergedCutProfiles.Batch126.profile5076,(fun _ => MergedCutProfiles.Batch126.profile5076)⟩
theorem profilesValid753 : retention753.ProfilesValid := by
  exact MergedCutProfiles.Batch126.valid5076
theorem numericValid753 : retention753.NumericValid := by decide +kernel
def certificate753 : RatCutBinCertificate := ⟨⟨retention753,(1067127128350819737/500000000000000000),(6511012982960937/62500000000000000),(12626426173190284547/1000000000000000000),(277681659324691596311/1000000000000000000),(1470208167327416159/1000000000000000000)⟩,(993099642606045611/1000000000000000000),(52195579160558421/125000000000000000),(54442183456371599/250000000000000000),(140857546569090313/1000000000000000000)⟩
theorem valid753 : certificate753.Valid := by decide +kernel
theorem sound753 : certificate753.Sound := rat_cut_bin_certificate_sound certificate753 profilesValid753 numericValid753 valid753

def retention754 : RatCutRetentionCertificate := ⟨(187/4000),(47/1000),(9976924352843487587/21961260129902898230),(565820103365832283/100000000000000000),1,(26793268042505425243/25600000000000000000),true,MergedCutProfiles.Batch126.profile5065,![MergedCutProfiles.Batch126.profile5065,MergedCutProfiles.Batch126.profile5071,MergedCutProfiles.Batch126.profile5077,MergedCutProfiles.Batch126.profile5078,MergedCutProfiles.Batch126.profile5079,MergedCutProfiles.Batch127.profile5080,MergedCutProfiles.Batch127.profile5081,MergedCutProfiles.Batch127.profile5082,MergedCutProfiles.Batch127.profile5083,MergedCutProfiles.Batch127.profile5084,MergedCutProfiles.Batch127.profile5085,MergedCutProfiles.Batch127.profile5086,MergedCutProfiles.Batch127.profile5087,MergedCutProfiles.Batch127.profile5088,MergedCutProfiles.Batch127.profile5089,MergedCutProfiles.Batch127.profile5090]⟩
theorem profilesValid754 : retention754.ProfilesValid := by
  change ∀ j : Fin 16, (retention754.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch126.valid5065
  · exact MergedCutProfiles.Batch126.valid5071
  · exact MergedCutProfiles.Batch126.valid5077
  · exact MergedCutProfiles.Batch126.valid5078
  · exact MergedCutProfiles.Batch126.valid5079
  · exact MergedCutProfiles.Batch127.valid5080
  · exact MergedCutProfiles.Batch127.valid5081
  · exact MergedCutProfiles.Batch127.valid5082
  · exact MergedCutProfiles.Batch127.valid5083
  · exact MergedCutProfiles.Batch127.valid5084
  · exact MergedCutProfiles.Batch127.valid5085
  · exact MergedCutProfiles.Batch127.valid5086
  · exact MergedCutProfiles.Batch127.valid5087
  · exact MergedCutProfiles.Batch127.valid5088
  · exact MergedCutProfiles.Batch127.valid5089
  · exact MergedCutProfiles.Batch127.valid5090
theorem numericValid754 : retention754.NumericValid := by decide +kernel
def certificate754 : RatCutBinCertificate := ⟨⟨retention754,(1067127128350819737/500000000000000000),(6511012982960937/62500000000000000),(12626426173190284547/1000000000000000000),(277681659324691596311/1000000000000000000),(102900188307205973/100000000000000000)⟩,(993099642606045611/1000000000000000000),(484343973871816541/1000000000000000000),(164525962520826013/1000000000000000000),(142173127021313969/1000000000000000000)⟩
theorem valid754 : certificate754.Valid := by decide +kernel
theorem sound754 : certificate754.Sound := rat_cut_bin_certificate_sound certificate754 profilesValid754 numericValid754 valid754

def retention755 : RatCutRetentionCertificate := ⟨(187/4000),(47/1000),(5401789718510331999/10980630064951449115),(9976924352843487587/1000000000000000000),(21/20),(16137994597733812563957966912751649104391/15963078964549580139200000000000000000000),false,MergedCutProfiles.Batch127.profile5091,(fun _ => MergedCutProfiles.Batch127.profile5091)⟩
theorem profilesValid755 : retention755.ProfilesValid := by
  exact MergedCutProfiles.Batch127.valid5091
theorem numericValid755 : retention755.NumericValid := by decide +kernel
def certificate755 : RatCutBinCertificate := ⟨⟨retention755,(1067127128350819737/500000000000000000),(6511012982960937/62500000000000000),(12626426173190284547/1000000000000000000),(277681659324691596311/1000000000000000000),(992467418690956971/1000000000000000000)⟩,(993099642606045611/1000000000000000000),(481183994503932673/1000000000000000000),(83413570778760401/500000000000000000),(28717528085360949/200000000000000000)⟩
theorem valid755 : certificate755.Valid := by decide +kernel
theorem sound755 : certificate755.Sound := rat_cut_bin_certificate_sound certificate755 profilesValid755 numericValid755 valid755

def certificates : List RatCutBinCertificate := [certificate744,certificate745,certificate746,certificate747,certificate748,certificate749,certificate750,certificate751,certificate752,certificate753,certificate754,certificate755]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound744,List.forall_mem_cons.mpr ⟨sound745,List.forall_mem_cons.mpr ⟨sound746,List.forall_mem_cons.mpr ⟨sound747,List.forall_mem_cons.mpr ⟨sound748,List.forall_mem_cons.mpr ⟨sound749,List.forall_mem_cons.mpr ⟨sound750,List.forall_mem_cons.mpr ⟨sound751,List.forall_mem_cons.mpr ⟨sound752,List.forall_mem_cons.mpr ⟨sound753,List.forall_mem_cons.mpr ⟨sound754,List.forall_mem_cons.mpr ⟨sound755,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch062
