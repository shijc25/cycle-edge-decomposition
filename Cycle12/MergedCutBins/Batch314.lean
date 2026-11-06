import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch017
import Cycle12.MergedCutProfiles.Batch316
import Cycle12.MergedCutProfiles.Batch317
import Cycle12.MergedCutProfiles.Batch452
import Cycle12.MergedCutProfiles.Batch573
import Cycle12.MergedCutProfiles.Batch574
import Cycle12.MergedCutProfiles.Batch575

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch314

def retention3768 : RatCutRetentionCertificate := ⟨(7/500),(29/2000),(64000000000000000000/5445927406376945481761),(8631626716470628079/500000000000000000),1,(30188787875030836852654851841796215683/13810602746353004926400000000000000000),false,MergedCutProfiles.Batch573.profile22959,(fun _ => MergedCutProfiles.Batch573.profile22959)⟩
theorem profilesValid3768 : retention3768.ProfilesValid := by
  exact MergedCutProfiles.Batch573.valid22959
theorem numericValid3768 : retention3768.NumericValid := by decide +kernel
def certificate3768 : RatCutBinCertificate := ⟨⟨retention3768,(1775054291453891259/1000000000000000000),(4334189134333581/500000000000000000),(395473373618377527/50000000000000000),(43173931529598022123071/1000000000000000000),(2183968483789235753/1000000000000000000)⟩,(499979608813001479/500000000000000000),(16286446287100007/500000000000000000),(836808635620293009/1000000000000000000),(1622255901522504099/1000000000000000000)⟩
theorem valid3768 : certificate3768.Valid := by decide +kernel
theorem sound3768 : certificate3768.Sound := rat_cut_bin_certificate_sound certificate3768 profilesValid3768 numericValid3768 valid3768

def retention3769 : RatCutRetentionCertificate := ⟨(7/500),(29/2000),(1/2),64,1,(15960618230641953517588502271429102831/16000000000000000000000000000000000000),false,MergedCutProfiles.Batch573.profile22958,(fun _ => MergedCutProfiles.Batch573.profile22958)⟩
theorem profilesValid3769 : retention3769.ProfilesValid := by
  exact MergedCutProfiles.Batch573.valid22958
theorem numericValid3769 : retention3769.NumericValid := by decide +kernel
def certificate3769 : RatCutBinCertificate := ⟨⟨retention3769,(1775054291453891259/1000000000000000000),(4334189134333581/500000000000000000),(395473373618377527/50000000000000000),(43173931529598022123071/1000000000000000000),(497796634621759153/500000000000000000)⟩,(499979608813001479/500000000000000000),(71453045139566061/1000000000000000000),(29327334305884881/40000000000000000),(359370768486332857/500000000000000000)⟩
theorem valid3769 : certificate3769.Valid := by decide +kernel
theorem sound3769 : certificate3769.Sound := rat_cut_bin_certificate_sound certificate3769 profilesValid3769 numericValid3769 valid3769

def retention3770 : RatCutRetentionCertificate := ⟨(29/2000),(3/200),(616689157823238401/5077149562473322864465),(281931728087379919/500000000000000000),4,(4933060440913603641836276207293131303/2255453824699039352000000000000000000),true,MergedCutProfiles.Batch574.profile22960,![MergedCutProfiles.Batch574.profile22960,MergedCutProfiles.Batch574.profile22961,MergedCutProfiles.Batch574.profile22962,MergedCutProfiles.Batch574.profile22963,MergedCutProfiles.Batch574.profile22964,MergedCutProfiles.Batch574.profile22965,MergedCutProfiles.Batch574.profile22966,MergedCutProfiles.Batch574.profile22967,MergedCutProfiles.Batch574.profile22968,MergedCutProfiles.Batch574.profile22969,MergedCutProfiles.Batch574.profile22970,MergedCutProfiles.Batch574.profile22971,MergedCutProfiles.Batch574.profile22972,MergedCutProfiles.Batch574.profile22973,MergedCutProfiles.Batch574.profile22973,MergedCutProfiles.Batch574.profile22974]⟩
theorem profilesValid3770 : retention3770.ProfilesValid := by
  change ∀ j : Fin 16, (retention3770.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch574.valid22960
  · exact MergedCutProfiles.Batch574.valid22961
  · exact MergedCutProfiles.Batch574.valid22962
  · exact MergedCutProfiles.Batch574.valid22963
  · exact MergedCutProfiles.Batch574.valid22964
  · exact MergedCutProfiles.Batch574.valid22965
  · exact MergedCutProfiles.Batch574.valid22966
  · exact MergedCutProfiles.Batch574.valid22967
  · exact MergedCutProfiles.Batch574.valid22968
  · exact MergedCutProfiles.Batch574.valid22969
  · exact MergedCutProfiles.Batch574.valid22970
  · exact MergedCutProfiles.Batch574.valid22971
  · exact MergedCutProfiles.Batch574.valid22972
  · exact MergedCutProfiles.Batch574.valid22973
  · exact MergedCutProfiles.Batch574.valid22973
  · exact MergedCutProfiles.Batch574.valid22974
theorem numericValid3770 : retention3770.NumericValid := by decide +kernel
def certificate3770 : RatCutBinCertificate := ⟨⟨retention3770,(1803500147910387847/1000000000000000000),(9292470143341151/1000000000000000000),(7959676044192463901/1000000000000000000),(40506127629414174175587/1000000000000000000),(54468696017935943/25000000000000000)⟩,(999955861803604517/1000000000000000000),(661006235986298317/1000000000000000000),(65342467002569401/1000000000000000000),(28666425610628741/1000000000000000000)⟩
theorem valid3770 : certificate3770.Valid := by decide +kernel
theorem sound3770 : certificate3770.Sound := rat_cut_bin_certificate_sound certificate3770 profilesValid3770 numericValid3770 valid3770

def retention3771 : RatCutRetentionCertificate := ⟨(29/2000),(3/200),(19564319800000000/78109993268820351761),(616689157823238401/1000000000000000000),4,(585522828382117096433/256000000000000000000),true,MergedCutProfiles.Batch574.profile22975,![MergedCutProfiles.Batch574.profile22975,MergedCutProfiles.Batch574.profile22963,MergedCutProfiles.Batch574.profile22966,MergedCutProfiles.Batch574.profile22968,MergedCutProfiles.Batch574.profile22970,MergedCutProfiles.Batch574.profile22971,MergedCutProfiles.Batch574.profile22973,MergedCutProfiles.Batch574.profile22974,MergedCutProfiles.Batch574.profile22976,MergedCutProfiles.Batch574.profile22977,MergedCutProfiles.Batch574.profile22978,MergedCutProfiles.Batch574.profile22979,MergedCutProfiles.Batch574.profile22980,MergedCutProfiles.Batch574.profile22981,MergedCutProfiles.Batch574.profile22982,MergedCutProfiles.Batch574.profile22983]⟩
theorem profilesValid3771 : retention3771.ProfilesValid := by
  change ∀ j : Fin 16, (retention3771.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch574.valid22975
  · exact MergedCutProfiles.Batch574.valid22963
  · exact MergedCutProfiles.Batch574.valid22966
  · exact MergedCutProfiles.Batch574.valid22968
  · exact MergedCutProfiles.Batch574.valid22970
  · exact MergedCutProfiles.Batch574.valid22971
  · exact MergedCutProfiles.Batch574.valid22973
  · exact MergedCutProfiles.Batch574.valid22974
  · exact MergedCutProfiles.Batch574.valid22976
  · exact MergedCutProfiles.Batch574.valid22977
  · exact MergedCutProfiles.Batch574.valid22978
  · exact MergedCutProfiles.Batch574.valid22979
  · exact MergedCutProfiles.Batch574.valid22980
  · exact MergedCutProfiles.Batch574.valid22981
  · exact MergedCutProfiles.Batch574.valid22982
  · exact MergedCutProfiles.Batch574.valid22983
theorem numericValid3771 : retention3771.NumericValid := by decide +kernel
def certificate3771 : RatCutBinCertificate := ⟨⟨retention3771,(1803500147910387847/1000000000000000000),(9292470143341151/1000000000000000000),(7959676044192463901/1000000000000000000),(40506127629414174175587/1000000000000000000),(1139388305610852723/500000000000000000)⟩,(999955861803604517/1000000000000000000),(23782552444837727/40000000000000000),(96306270576299411/1000000000000000000),(22284539106177887/500000000000000000)⟩
theorem valid3771 : certificate3771.Valid := by decide +kernel
theorem sound3771 : certificate3771.Sound := rat_cut_bin_certificate_sound certificate3771 profilesValid3771 numericValid3771 valid3771

def retention3772 : RatCutRetentionCertificate := ⟨(29/2000),(3/200),(1123159121411108591/1015429912494664572893),(1271680787/1000000000),(5/2),(117095291696899737/50000000000000000),true,MergedCutProfiles.Batch574.profile22969,![MergedCutProfiles.Batch574.profile22969,MergedCutProfiles.Batch574.profile22976,MergedCutProfiles.Batch574.profile22980,MergedCutProfiles.Batch574.profile22984,MergedCutProfiles.Batch574.profile22985,MergedCutProfiles.Batch574.profile22986,MergedCutProfiles.Batch574.profile22987,MergedCutProfiles.Batch574.profile22988,MergedCutProfiles.Batch574.profile22989,MergedCutProfiles.Batch574.profile22990,MergedCutProfiles.Batch574.profile22991,MergedCutProfiles.Batch574.profile22992,MergedCutProfiles.Batch574.profile22993,MergedCutProfiles.Batch574.profile22994,MergedCutProfiles.Batch574.profile22995,MergedCutProfiles.Batch574.profile22996]⟩
theorem profilesValid3772 : retention3772.ProfilesValid := by
  change ∀ j : Fin 16, (retention3772.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch574.valid22969
  · exact MergedCutProfiles.Batch574.valid22976
  · exact MergedCutProfiles.Batch574.valid22980
  · exact MergedCutProfiles.Batch574.valid22984
  · exact MergedCutProfiles.Batch574.valid22985
  · exact MergedCutProfiles.Batch574.valid22986
  · exact MergedCutProfiles.Batch574.valid22987
  · exact MergedCutProfiles.Batch574.valid22988
  · exact MergedCutProfiles.Batch574.valid22989
  · exact MergedCutProfiles.Batch574.valid22990
  · exact MergedCutProfiles.Batch574.valid22991
  · exact MergedCutProfiles.Batch574.valid22992
  · exact MergedCutProfiles.Batch574.valid22993
  · exact MergedCutProfiles.Batch574.valid22994
  · exact MergedCutProfiles.Batch574.valid22995
  · exact MergedCutProfiles.Batch574.valid22996
theorem numericValid3772 : retention3772.NumericValid := by decide +kernel
def certificate3772 : RatCutBinCertificate := ⟨⟨retention3772,(1803500147910387847/1000000000000000000),(9292470143341151/1000000000000000000),(7959676044192463901/1000000000000000000),(40506127629414174175587/1000000000000000000),(2336642123331483313/1000000000000000000)⟩,(999955861803604517/1000000000000000000),(379170454630214361/1000000000000000000),(126559563779641561/500000000000000000),(91410081811046171/500000000000000000)⟩
theorem valid3772 : certificate3772.Valid := by decide +kernel
theorem sound3772 : certificate3772.Sound := rat_cut_bin_certificate_sound certificate3772 profilesValid3772 numericValid3772 valid3772

def retention3773 : RatCutRetentionCertificate := ⟨(29/2000),(3/200),(12800000000000000000/1015429912494664572893),(1123159121411108591/200000000000000000),(6/5),(49463712705899815393870048017573684551/22463182428222171820000000000000000000),true,MergedCutProfiles.Batch574.profile22997,![MergedCutProfiles.Batch574.profile22997,MergedCutProfiles.Batch574.profile22998,MergedCutProfiles.Batch574.profile22999,MergedCutProfiles.Batch575.profile23000,MergedCutProfiles.Batch575.profile23001,MergedCutProfiles.Batch575.profile23002,MergedCutProfiles.Batch575.profile23003,MergedCutProfiles.Batch575.profile23004,MergedCutProfiles.Batch575.profile23005,MergedCutProfiles.Batch575.profile23006,MergedCutProfiles.Batch575.profile23007,MergedCutProfiles.Batch575.profile23008,MergedCutProfiles.Batch575.profile23009,MergedCutProfiles.Batch575.profile23010,MergedCutProfiles.Batch575.profile23011,MergedCutProfiles.Batch575.profile23012]⟩
theorem profilesValid3773 : retention3773.ProfilesValid := by
  change ∀ j : Fin 16, (retention3773.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch574.valid22997
  · exact MergedCutProfiles.Batch574.valid22998
  · exact MergedCutProfiles.Batch574.valid22999
  · exact MergedCutProfiles.Batch575.valid23000
  · exact MergedCutProfiles.Batch575.valid23001
  · exact MergedCutProfiles.Batch575.valid23002
  · exact MergedCutProfiles.Batch575.valid23003
  · exact MergedCutProfiles.Batch575.valid23004
  · exact MergedCutProfiles.Batch575.valid23005
  · exact MergedCutProfiles.Batch575.valid23006
  · exact MergedCutProfiles.Batch575.valid23007
  · exact MergedCutProfiles.Batch575.valid23008
  · exact MergedCutProfiles.Batch575.valid23009
  · exact MergedCutProfiles.Batch575.valid23010
  · exact MergedCutProfiles.Batch575.valid23011
  · exact MergedCutProfiles.Batch575.valid23012
theorem numericValid3773 : retention3773.NumericValid := by decide +kernel
def certificate3773 : RatCutBinCertificate := ⟨⟨retention3773,(1803500147910387847/1000000000000000000),(9292470143341151/1000000000000000000),(7959676044192463901/1000000000000000000),(40506127629414174175587/1000000000000000000),(109973192387067687/50000000000000000)⟩,(999955861803604517/1000000000000000000),(247552702602095099/1000000000000000000),(16269629982557787/40000000000000000),(18314761810996963/31250000000000000)⟩
theorem valid3773 : certificate3773.Valid := by decide +kernel
theorem sound3773 : certificate3773.Sound := rat_cut_bin_certificate_sound certificate3773 profilesValid3773 numericValid3773 valid3773

def retention3774 : RatCutRetentionCertificate := ⟨(29/2000),(3/200),(1/2),64,1,(63842501012626550423494356850201009159/64000000000000000000000000000000000000),false,MergedCutProfiles.Batch575.profile23013,(fun _ => MergedCutProfiles.Batch575.profile23013)⟩
theorem profilesValid3774 : retention3774.ProfilesValid := by
  exact MergedCutProfiles.Batch575.valid23013
theorem numericValid3774 : retention3774.NumericValid := by decide +kernel
def certificate3774 : RatCutBinCertificate := ⟨⟨retention3774,(1803500147910387847/1000000000000000000),(9292470143341151/1000000000000000000),(7959676044192463901/1000000000000000000),(40506127629414174175587/1000000000000000000),(995433594224068403/1000000000000000000)⟩,(999955861803604517/1000000000000000000),(227682225942112417/500000000000000000),(37283919040391797/200000000000000000),(182718132036028069/1000000000000000000)⟩
theorem valid3774 : certificate3774.Valid := by decide +kernel
theorem sound3774 : certificate3774.Sound := rat_cut_bin_certificate_sound certificate3774 profilesValid3774 numericValid3774 valid3774

def retention3775 : RatCutRetentionCertificate := ⟨(29/2000),(3/200),(12800000000000000000/1015429912494664572893),(17425155873001604501/1000000000000000000),1,(152014130504369316189866191207140954843/69700623492006418004000000000000000000),false,MergedCutProfiles.Batch575.profile23014,(fun _ => MergedCutProfiles.Batch575.profile23014)⟩
theorem profilesValid3775 : retention3775.ProfilesValid := by
  exact MergedCutProfiles.Batch575.valid23014
theorem numericValid3775 : retention3775.NumericValid := by decide +kernel
def certificate3775 : RatCutBinCertificate := ⟨⟨retention3775,(1776732248910387847/1000000000000000000),(9292470143341151/1000000000000000000),(7959676044192463901/1000000000000000000),(40506127629414174175587/1000000000000000000),(2178883738546775393/1000000000000000000)⟩,(999956516911525497/1000000000000000000),(16213993591879143/500000000000000000),(2616331737252543/3125000000000000),(1621393803074744341/1000000000000000000)⟩
theorem valid3775 : certificate3775.Valid := by decide +kernel
theorem sound3775 : certificate3775.Sound := rat_cut_bin_certificate_sound certificate3775 profilesValid3775 numericValid3775 valid3775

def retention3776 : RatCutRetentionCertificate := ⟨(29/2000),(3/200),(1/2),64,1,(63842501012626550423494356850201009159/64000000000000000000000000000000000000),false,MergedCutProfiles.Batch575.profile23013,(fun _ => MergedCutProfiles.Batch575.profile23013)⟩
theorem profilesValid3776 : retention3776.ProfilesValid := by
  exact MergedCutProfiles.Batch575.valid23013
theorem numericValid3776 : retention3776.NumericValid := by decide +kernel
def certificate3776 : RatCutBinCertificate := ⟨⟨retention3776,(1776732248910387847/1000000000000000000),(9292470143341151/1000000000000000000),(7959676044192463901/1000000000000000000),(40506127629414174175587/1000000000000000000),(995464844227431363/1000000000000000000)⟩,(999956516911525497/1000000000000000000),(70978713470619949/1000000000000000000),(183588650768424133/250000000000000000),(179949077953537877/250000000000000000)⟩
theorem valid3776 : certificate3776.Valid := by decide +kernel
theorem sound3776 : certificate3776.Sound := rat_cut_bin_certificate_sound certificate3776 profilesValid3776 numericValid3776 valid3776

def retention3777 : RatCutRetentionCertificate := ⟨(3/200),(2/125),(26363285681154973/185068222956082229703),(561505858876437607/1000000000000000000),4,(19138538664012857745956823415020163/8773529044944337609375000000000000),true,MergedCutProfiles.Batch575.profile23015,![MergedCutProfiles.Batch575.profile23015,MergedCutProfiles.Batch575.profile23016,MergedCutProfiles.Batch575.profile23017,MergedCutProfiles.Batch575.profile23018,MergedCutProfiles.Batch575.profile23019,MergedCutProfiles.Batch575.profile23020,MergedCutProfiles.Batch452.profile18090,MergedCutProfiles.Batch452.profile18098,MergedCutProfiles.Batch575.profile23021,MergedCutProfiles.Batch316.profile12667,MergedCutProfiles.Batch452.profile18091,MergedCutProfiles.Batch575.profile23022,MergedCutProfiles.Batch575.profile23023,MergedCutProfiles.Batch575.profile23023,MergedCutProfiles.Batch452.profile18092,MergedCutProfiles.Batch452.profile18099]⟩
theorem profilesValid3777 : retention3777.ProfilesValid := by
  change ∀ j : Fin 16, (retention3777.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch575.valid23015
  · exact MergedCutProfiles.Batch575.valid23016
  · exact MergedCutProfiles.Batch575.valid23017
  · exact MergedCutProfiles.Batch575.valid23018
  · exact MergedCutProfiles.Batch575.valid23019
  · exact MergedCutProfiles.Batch575.valid23020
  · exact MergedCutProfiles.Batch452.valid18090
  · exact MergedCutProfiles.Batch452.valid18098
  · exact MergedCutProfiles.Batch575.valid23021
  · exact MergedCutProfiles.Batch316.valid12667
  · exact MergedCutProfiles.Batch452.valid18091
  · exact MergedCutProfiles.Batch575.valid23022
  · exact MergedCutProfiles.Batch575.valid23023
  · exact MergedCutProfiles.Batch575.valid23023
  · exact MergedCutProfiles.Batch452.valid18092
  · exact MergedCutProfiles.Batch452.valid18099
theorem numericValid3777 : retention3777.NumericValid := by decide +kernel
def certificate3777 : RatCutBinCertificate := ⟨⟨retention3777,(360673200239784127/200000000000000000),(1060946273715283/100000000000000000),(200259423284588121/25000000000000000),(7149002648276999136387/200000000000000000),(2171841734159204929/1000000000000000000)⟩,(999950017947899449/1000000000000000000),(669845014805145877/1000000000000000000),(15435529091601597/250000000000000000),(3374441307437787/125000000000000000)⟩
theorem valid3777 : certificate3777.Valid := by decide +kernel
theorem sound3777 : certificate3777.Sound := rat_cut_bin_certificate_sound certificate3777 profilesValid3777 numericValid3777 valid3777

def retention3778 : RatCutRetentionCertificate := ⟨(3/200),(2/125),(158409498625000000/555204668868246689109),(79089857043464919/125000000000000000),4,(1169349145858837364807788437191259403/506175085078175481600000000000000000),true,MergedCutProfiles.Batch575.profile23016,![MergedCutProfiles.Batch575.profile23016,MergedCutProfiles.Batch575.profile23018,MergedCutProfiles.Batch575.profile23020,MergedCutProfiles.Batch452.profile18098,MergedCutProfiles.Batch316.profile12667,MergedCutProfiles.Batch575.profile23022,MergedCutProfiles.Batch575.profile23023,MergedCutProfiles.Batch452.profile18099,MergedCutProfiles.Batch575.profile23024,MergedCutProfiles.Batch017.profile703,MergedCutProfiles.Batch452.profile18108,MergedCutProfiles.Batch317.profile12686,MergedCutProfiles.Batch452.profile18094,MergedCutProfiles.Batch575.profile23025,MergedCutProfiles.Batch316.profile12668,MergedCutProfiles.Batch452.profile18100]⟩
theorem profilesValid3778 : retention3778.ProfilesValid := by
  change ∀ j : Fin 16, (retention3778.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch575.valid23016
  · exact MergedCutProfiles.Batch575.valid23018
  · exact MergedCutProfiles.Batch575.valid23020
  · exact MergedCutProfiles.Batch452.valid18098
  · exact MergedCutProfiles.Batch316.valid12667
  · exact MergedCutProfiles.Batch575.valid23022
  · exact MergedCutProfiles.Batch575.valid23023
  · exact MergedCutProfiles.Batch452.valid18099
  · exact MergedCutProfiles.Batch575.valid23024
  · exact MergedCutProfiles.Batch017.valid703
  · exact MergedCutProfiles.Batch452.valid18108
  · exact MergedCutProfiles.Batch317.valid12686
  · exact MergedCutProfiles.Batch452.valid18094
  · exact MergedCutProfiles.Batch575.valid23025
  · exact MergedCutProfiles.Batch316.valid12668
  · exact MergedCutProfiles.Batch452.valid18100
theorem numericValid3778 : retention3778.NumericValid := by decide +kernel
def certificate3778 : RatCutBinCertificate := ⟨⟨retention3778,(360673200239784127/200000000000000000),(1060946273715283/100000000000000000),(200259423284588121/25000000000000000),(7149002648276999136387/200000000000000000),(575153337846164343/250000000000000000)⟩,(999950017947899449/1000000000000000000),(291553023856451959/500000000000000000),(4094983585851619/40000000000000000),(2398752595620279/50000000000000000)⟩
theorem valid3778 : certificate3778.Valid := by decide +kernel
theorem sound3778 : certificate3778.Sound := rat_cut_bin_certificate_sound certificate3778 profilesValid3778 numericValid3778 valid3778

def retention3779 : RatCutRetentionCertificate := ⟨(3/200),(2/125),(2556638215227126553/2220818675472986756436),(1267275989/1000000000),(51/20),(11920304627397673246315799298110758719/5069103956000000000000000000000000000),true,MergedCutProfiles.Batch452.profile18098,![MergedCutProfiles.Batch452.profile18098,MergedCutProfiles.Batch452.profile18099,MergedCutProfiles.Batch575.profile23026,MergedCutProfiles.Batch452.profile18100,MergedCutProfiles.Batch017.profile704,MergedCutProfiles.Batch452.profile18101,MergedCutProfiles.Batch452.profile18102,MergedCutProfiles.Batch575.profile23027,MergedCutProfiles.Batch575.profile23028,MergedCutProfiles.Batch017.profile706,MergedCutProfiles.Batch316.profile12671,MergedCutProfiles.Batch316.profile12672,MergedCutProfiles.Batch575.profile23029,MergedCutProfiles.Batch452.profile18106,MergedCutProfiles.Batch017.profile708,MergedCutProfiles.Batch316.profile12675]⟩
theorem profilesValid3779 : retention3779.ProfilesValid := by
  change ∀ j : Fin 16, (retention3779.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch452.valid18098
  · exact MergedCutProfiles.Batch452.valid18099
  · exact MergedCutProfiles.Batch575.valid23026
  · exact MergedCutProfiles.Batch452.valid18100
  · exact MergedCutProfiles.Batch017.valid704
  · exact MergedCutProfiles.Batch452.valid18101
  · exact MergedCutProfiles.Batch452.valid18102
  · exact MergedCutProfiles.Batch575.valid23027
  · exact MergedCutProfiles.Batch575.valid23028
  · exact MergedCutProfiles.Batch017.valid706
  · exact MergedCutProfiles.Batch316.valid12671
  · exact MergedCutProfiles.Batch316.valid12672
  · exact MergedCutProfiles.Batch575.valid23029
  · exact MergedCutProfiles.Batch452.valid18106
  · exact MergedCutProfiles.Batch017.valid708
  · exact MergedCutProfiles.Batch316.valid12675
theorem numericValid3779 : retention3779.NumericValid := by decide +kernel
def certificate3779 : RatCutBinCertificate := ⟨⟨retention3779,(360673200239784127/200000000000000000),(1060946273715283/100000000000000000),(200259423284588121/25000000000000000),(7149002648276999136387/200000000000000000),(2345469836294604259/1000000000000000000)⟩,(999950017947899449/1000000000000000000),(76248417257823849/200000000000000000),(125557959889936637/500000000000000000),(44947105608615549/250000000000000000)⟩
theorem valid3779 : certificate3779.Valid := by decide +kernel
theorem sound3779 : certificate3779.Sound := rat_cut_bin_certificate_sound certificate3779 profilesValid3779 numericValid3779 valid3779

def certificates : List RatCutBinCertificate := [certificate3768,certificate3769,certificate3770,certificate3771,certificate3772,certificate3773,certificate3774,certificate3775,certificate3776,certificate3777,certificate3778,certificate3779]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound3768,List.forall_mem_cons.mpr ⟨sound3769,List.forall_mem_cons.mpr ⟨sound3770,List.forall_mem_cons.mpr ⟨sound3771,List.forall_mem_cons.mpr ⟨sound3772,List.forall_mem_cons.mpr ⟨sound3773,List.forall_mem_cons.mpr ⟨sound3774,List.forall_mem_cons.mpr ⟨sound3775,List.forall_mem_cons.mpr ⟨sound3776,List.forall_mem_cons.mpr ⟨sound3777,List.forall_mem_cons.mpr ⟨sound3778,List.forall_mem_cons.mpr ⟨sound3779,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch314
