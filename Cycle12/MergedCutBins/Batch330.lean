import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch070
import Cycle12.MergedCutProfiles.Batch346
import Cycle12.MergedCutProfiles.Batch347
import Cycle12.MergedCutProfiles.Batch348
import Cycle12.MergedCutProfiles.Batch349
import Cycle12.MergedCutProfiles.Batch350
import Cycle12.MergedCutProfiles.Batch470
import Cycle12.MergedCutProfiles.Batch471
import Cycle12.MergedCutProfiles.Batch472
import Cycle12.MergedCutProfiles.Batch600
import Cycle12.MergedCutProfiles.Batch601
import Cycle12.MergedCutProfiles.Batch602

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch330

def retention3960 : RatCutRetentionCertificate := ⟨(9/250),(37/1000),(4000000000000000000/46774558057064058789),(23049447370537983081/1000000000000000000),1,(5510968542838018963421429521805788417/2881180921317247885125000000000000000),false,MergedCutProfiles.Batch600.profile24034,(fun _ => MergedCutProfiles.Batch600.profile24034)⟩
theorem profilesValid3960 : retention3960.ProfilesValid := by
  exact MergedCutProfiles.Batch600.valid24034
theorem numericValid3960 : retention3960.NumericValid := by decide +kernel
def certificate3960 : RatCutBinCertificate := ⟨⟨retention3960,(1822146844483647183/1000000000000000000),(61591158108543061/1000000000000000000),(2671917448581533249/250000000000000000),(1608156605809442427953/200000000000000000),(190224572269407373/100000000000000000)⟩,(124973317425004849/125000000000000000),(15960924057386067/500000000000000000),(838686493441315713/1000000000000000000),(736718802182056621/500000000000000000)⟩
theorem valid3960 : certificate3960.Valid := by decide +kernel
theorem sound3960 : certificate3960.Sound := rat_cut_bin_certificate_sound certificate3960 profilesValid3960 numericValid3960 valid3960

def retention3961 : RatCutRetentionCertificate := ⟨(9/250),(37/1000),(1/2),64,1,(15961296343634275519387494158967405759/16000000000000000000000000000000000000),false,MergedCutProfiles.Batch070.profile2821,(fun _ => MergedCutProfiles.Batch070.profile2821)⟩
theorem profilesValid3961 : retention3961.ProfilesValid := by
  exact MergedCutProfiles.Batch070.valid2821
theorem numericValid3961 : retention3961.NumericValid := by decide +kernel
def certificate3961 : RatCutBinCertificate := ⟨⟨retention3961,(1822146844483647183/1000000000000000000),(61591158108543061/1000000000000000000),(2671917448581533249/250000000000000000),(1608156605809442427953/200000000000000000),(987080308975041039/1000000000000000000)⟩,(124973317425004849/125000000000000000),(61517992492291321/1000000000000000000),(15163328704118969/20000000000000000),(368422714155115491/500000000000000000)⟩
theorem valid3961 : certificate3961.Valid := by decide +kernel
theorem sound3961 : certificate3961.Sound := rat_cut_bin_certificate_sound certificate3961 profilesValid3961 numericValid3961 valid3961

def retention3962 : RatCutRetentionCertificate := ⟨(37/1000),(19/500),(82976887457386814/100825004167426114541),(287543669406785989/500000000000000000),4,(5096400994881052207412119324201168303/2300349355254287912000000000000000000),true,MergedCutProfiles.Batch600.profile24035,![MergedCutProfiles.Batch600.profile24035,MergedCutProfiles.Batch600.profile24036,MergedCutProfiles.Batch600.profile24037,MergedCutProfiles.Batch600.profile24038,MergedCutProfiles.Batch600.profile24039,MergedCutProfiles.Batch601.profile24040,MergedCutProfiles.Batch470.profile18822,MergedCutProfiles.Batch470.profile18834,MergedCutProfiles.Batch601.profile24041,MergedCutProfiles.Batch471.profile18840,MergedCutProfiles.Batch601.profile24042,MergedCutProfiles.Batch601.profile24043,MergedCutProfiles.Batch346.profile13867,MergedCutProfiles.Batch601.profile24044,MergedCutProfiles.Batch601.profile24045,MergedCutProfiles.Batch347.profile13883]⟩
theorem profilesValid3962 : retention3962.ProfilesValid := by
  change ∀ j : Fin 16, (retention3962.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch600.valid24035
  · exact MergedCutProfiles.Batch600.valid24036
  · exact MergedCutProfiles.Batch600.valid24037
  · exact MergedCutProfiles.Batch600.valid24038
  · exact MergedCutProfiles.Batch600.valid24039
  · exact MergedCutProfiles.Batch601.valid24040
  · exact MergedCutProfiles.Batch470.valid18822
  · exact MergedCutProfiles.Batch470.valid18834
  · exact MergedCutProfiles.Batch601.valid24041
  · exact MergedCutProfiles.Batch471.valid18840
  · exact MergedCutProfiles.Batch601.valid24042
  · exact MergedCutProfiles.Batch601.valid24043
  · exact MergedCutProfiles.Batch346.valid13867
  · exact MergedCutProfiles.Batch601.valid24044
  · exact MergedCutProfiles.Batch601.valid24045
  · exact MergedCutProfiles.Batch347.valid13883
theorem numericValid3962 : retention3962.NumericValid := by decide +kernel
def certificate3962 : RatCutBinCertificate := ⟨⟨retention3962,(1865048927092262747/1000000000000000000),(65254397982896969/1000000000000000000),(10848204027206511119/1000000000000000000),(7697040557318305362201/1000000000000000000),(2170615072854770859/1000000000000000000)⟩,(99977261331393971/100000000000000000),(727624717573288087/1000000000000000000),(10253137931585713/250000000000000000),(9001319346741681/500000000000000000)⟩
theorem valid3962 : certificate3962.Valid := by decide +kernel
theorem sound3962 : certificate3962.Sound := rat_cut_bin_certificate_sound certificate3962 profilesValid3962 numericValid3962 valid3962

def retention3963 : RatCutRetentionCertificate := ⟨(37/1000),(19/500),(1147456911000000000/705775029171982801787),(290419106100853849/500000000000000000),4,(56872697848693284789/25600000000000000000),true,MergedCutProfiles.Batch600.profile24036,![MergedCutProfiles.Batch600.profile24036,MergedCutProfiles.Batch600.profile24038,MergedCutProfiles.Batch601.profile24040,MergedCutProfiles.Batch470.profile18834,MergedCutProfiles.Batch471.profile18840,MergedCutProfiles.Batch601.profile24043,MergedCutProfiles.Batch601.profile24044,MergedCutProfiles.Batch347.profile13883,MergedCutProfiles.Batch601.profile24046,MergedCutProfiles.Batch470.profile18824,MergedCutProfiles.Batch601.profile24047,MergedCutProfiles.Batch470.profile18810,MergedCutProfiles.Batch346.profile13868,MergedCutProfiles.Batch601.profile24048,MergedCutProfiles.Batch601.profile24049,MergedCutProfiles.Batch347.profile13884]⟩
theorem profilesValid3963 : retention3963.ProfilesValid := by
  change ∀ j : Fin 16, (retention3963.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch600.valid24036
  · exact MergedCutProfiles.Batch600.valid24038
  · exact MergedCutProfiles.Batch601.valid24040
  · exact MergedCutProfiles.Batch470.valid18834
  · exact MergedCutProfiles.Batch471.valid18840
  · exact MergedCutProfiles.Batch601.valid24043
  · exact MergedCutProfiles.Batch601.valid24044
  · exact MergedCutProfiles.Batch347.valid13883
  · exact MergedCutProfiles.Batch601.valid24046
  · exact MergedCutProfiles.Batch470.valid18824
  · exact MergedCutProfiles.Batch601.valid24047
  · exact MergedCutProfiles.Batch470.valid18810
  · exact MergedCutProfiles.Batch346.valid13868
  · exact MergedCutProfiles.Batch601.valid24048
  · exact MergedCutProfiles.Batch601.valid24049
  · exact MergedCutProfiles.Batch347.valid13884
theorem numericValid3963 : retention3963.NumericValid := by decide +kernel
def certificate3963 : RatCutBinCertificate := ⟨⟨retention3963,(1865048927092262747/1000000000000000000),(65254397982896969/1000000000000000000),(10848204027206511119/1000000000000000000),(7697040557318305362201/1000000000000000000),(2176714833420536121/1000000000000000000)⟩,(99977261331393971/100000000000000000),(144153258989102233/200000000000000000),(2701609275679379/62500000000000000),(19053348167665291/1000000000000000000)⟩
theorem valid3963 : certificate3963.Valid := by decide +kernel
theorem sound3963 : certificate3963.Sound := rat_cut_bin_certificate_sound certificate3963 profilesValid3963 numericValid3963 valid3963

def retention3964 : RatCutRetentionCertificate := ⟨(37/1000),(19/500),(1898010716255558084/705775029171982801787),(1147456911/1000000000),(11/4),(18824089148817536893/8000000000000000000),true,MergedCutProfiles.Batch601.profile24050,![MergedCutProfiles.Batch601.profile24050,MergedCutProfiles.Batch601.profile24051,MergedCutProfiles.Batch470.profile18808,MergedCutProfiles.Batch470.profile18823,MergedCutProfiles.Batch601.profile24052,MergedCutProfiles.Batch470.profile18824,MergedCutProfiles.Batch601.profile24053,MergedCutProfiles.Batch601.profile24054,MergedCutProfiles.Batch601.profile24049,MergedCutProfiles.Batch601.profile24055,MergedCutProfiles.Batch601.profile24056,MergedCutProfiles.Batch346.profile13869,MergedCutProfiles.Batch470.profile18814,MergedCutProfiles.Batch601.profile24057,MergedCutProfiles.Batch601.profile24058,MergedCutProfiles.Batch470.profile18816]⟩
theorem profilesValid3964 : retention3964.ProfilesValid := by
  change ∀ j : Fin 16, (retention3964.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch601.valid24050
  · exact MergedCutProfiles.Batch601.valid24051
  · exact MergedCutProfiles.Batch470.valid18808
  · exact MergedCutProfiles.Batch470.valid18823
  · exact MergedCutProfiles.Batch601.valid24052
  · exact MergedCutProfiles.Batch470.valid18824
  · exact MergedCutProfiles.Batch601.valid24053
  · exact MergedCutProfiles.Batch601.valid24054
  · exact MergedCutProfiles.Batch601.valid24049
  · exact MergedCutProfiles.Batch601.valid24055
  · exact MergedCutProfiles.Batch601.valid24056
  · exact MergedCutProfiles.Batch346.valid13869
  · exact MergedCutProfiles.Batch470.valid18814
  · exact MergedCutProfiles.Batch601.valid24057
  · exact MergedCutProfiles.Batch601.valid24058
  · exact MergedCutProfiles.Batch470.valid18816
theorem numericValid3964 : retention3964.NumericValid := by decide +kernel
def certificate3964 : RatCutBinCertificate := ⟨⟨retention3964,(1865048927092262747/1000000000000000000),(65254397982896969/1000000000000000000),(10848204027206511119/1000000000000000000),(7697040557318305362201/1000000000000000000),(2322159661462982071/1000000000000000000)⟩,(99977261331393971/100000000000000000),(226271696875506557/500000000000000000),(47161883668442957/250000000000000000),(62817928612498633/500000000000000000)⟩
theorem valid3964 : certificate3964.Valid := by decide +kernel
theorem sound3964 : certificate3964.Sound := rat_cut_bin_certificate_sound certificate3964 profilesValid3964 numericValid3964 valid3964

def retention3965 : RatCutRetentionCertificate := ⟨(37/1000),(19/500),(64000000000000000000/705775029171982801787),(474502679063889521/250000000000000000),(19/10),(91648338672283639883546496653988292239/47450267906388952100000000000000000000),false,MergedCutProfiles.Batch601.profile24059,(fun _ => MergedCutProfiles.Batch601.profile24059)⟩
theorem profilesValid3965 : retention3965.ProfilesValid := by
  exact MergedCutProfiles.Batch601.valid24059
theorem numericValid3965 : retention3965.NumericValid := by decide +kernel
def certificate3965 : RatCutBinCertificate := ⟨⟨retention3965,(1865048927092262747/1000000000000000000),(65254397982896969/1000000000000000000),(10848204027206511119/1000000000000000000),(7697040557318305362201/1000000000000000000),(955072684820360851/500000000000000000)⟩,(99977261331393971/100000000000000000),(110055545504622357/250000000000000000),(49646455754118549/250000000000000000),(78041149760209427/500000000000000000)⟩
theorem valid3965 : certificate3965.Valid := by decide +kernel
theorem sound3965 : certificate3965.Sound := rat_cut_bin_certificate_sound certificate3965 profilesValid3965 numericValid3965 valid3965

def retention3966 : RatCutRetentionCertificate := ⟨(37/1000),(19/500),(1/2),64,1,(255381539274569722621815190999861472551/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch348.profile13941,(fun _ => MergedCutProfiles.Batch348.profile13941)⟩
theorem profilesValid3966 : retention3966.ProfilesValid := by
  exact MergedCutProfiles.Batch348.valid13941
theorem numericValid3966 : retention3966.NumericValid := by decide +kernel
def certificate3966 : RatCutBinCertificate := ⟨⟨retention3966,(1865048927092262747/1000000000000000000),(65254397982896969/1000000000000000000),(10848204027206511119/1000000000000000000),(7697040557318305362201/1000000000000000000),(61647840354274581/62500000000000000)⟩,(99977261331393971/100000000000000000),(536691615133465523/1000000000000000000),(64654103958217637/500000000000000000),(15697554225775909/125000000000000000)⟩
theorem valid3966 : certificate3966.Valid := by decide +kernel
theorem sound3966 : certificate3966.Sound := rat_cut_bin_certificate_sound certificate3966 profilesValid3966 numericValid3966 valid3966

def retention3967 : RatCutRetentionCertificate := ⟨(37/1000),(19/500),(64000000000000000000/705775029171982801787),(23296051771607351497/1000000000000000000),1,(138183361821654061238681030367071463/72800161786272973428125000000000000),false,MergedCutProfiles.Batch601.profile24059,(fun _ => MergedCutProfiles.Batch601.profile24059)⟩
theorem profilesValid3967 : retention3967.ProfilesValid := by
  exact MergedCutProfiles.Batch601.valid24059
theorem numericValid3967 : retention3967.NumericValid := by decide +kernel
def certificate3967 : RatCutBinCertificate := ⟨⟨retention3967,(1824047190092262747/1000000000000000000),(65254397982896969/1000000000000000000),(10848204027206511119/1000000000000000000),(7697040557318305362201/1000000000000000000),(1887146823763528091/1000000000000000000)⟩,(62486100769808751/62500000000000000),(3989233136642989/125000000000000000),(167741910238739317/200000000000000000),(365956731950767803/250000000000000000)⟩
theorem valid3967 : certificate3967.Valid := by decide +kernel
theorem sound3967 : certificate3967.Sound := rat_cut_bin_certificate_sound certificate3967 profilesValid3967 numericValid3967 valid3967

def retention3968 : RatCutRetentionCertificate := ⟨(37/1000),(19/500),(1/2),64,1,(255381539274569722621815190999861472551/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch348.profile13941,(fun _ => MergedCutProfiles.Batch348.profile13941)⟩
theorem profilesValid3968 : retention3968.ProfilesValid := by
  exact MergedCutProfiles.Batch348.valid13941
theorem numericValid3968 : retention3968.NumericValid := by decide +kernel
def certificate3968 : RatCutBinCertificate := ⟨⟨retention3968,(1824047190092262747/1000000000000000000),(65254397982896969/1000000000000000000),(10848204027206511119/1000000000000000000),(7697040557318305362201/1000000000000000000),(493306040205989153/500000000000000000)⟩,(62486100769808751/62500000000000000),(61043393183869907/1000000000000000000),(379692034913674941/500000000000000000),(737677387466830617/1000000000000000000)⟩
theorem valid3968 : certificate3968.Valid := by decide +kernel
theorem sound3968 : certificate3968.Sound := rat_cut_bin_certificate_sound certificate3968 profilesValid3968 numericValid3968 valid3968

def retention3969 : RatCutRetentionCertificate := ⟨(19/500),(39/1000),(97386406503107206/111080860725864253343),(72316638492406341/125000000000000000),4,(1714794383080170885741581537121403173/771377477252334304000000000000000000),true,MergedCutProfiles.Batch601.profile24060,![MergedCutProfiles.Batch601.profile24060,MergedCutProfiles.Batch601.profile24061,MergedCutProfiles.Batch601.profile24062,MergedCutProfiles.Batch601.profile24063,MergedCutProfiles.Batch471.profile18865,MergedCutProfiles.Batch601.profile24064,MergedCutProfiles.Batch601.profile24065,MergedCutProfiles.Batch472.profile18890,MergedCutProfiles.Batch601.profile24066,MergedCutProfiles.Batch601.profile24067,MergedCutProfiles.Batch472.profile18901,MergedCutProfiles.Batch601.profile24068,MergedCutProfiles.Batch348.profile13945,MergedCutProfiles.Batch601.profile24069,MergedCutProfiles.Batch601.profile24070,MergedCutProfiles.Batch349.profile13961]⟩
theorem profilesValid3969 : retention3969.ProfilesValid := by
  change ∀ j : Fin 16, (retention3969.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch601.valid24060
  · exact MergedCutProfiles.Batch601.valid24061
  · exact MergedCutProfiles.Batch601.valid24062
  · exact MergedCutProfiles.Batch601.valid24063
  · exact MergedCutProfiles.Batch471.valid18865
  · exact MergedCutProfiles.Batch601.valid24064
  · exact MergedCutProfiles.Batch601.valid24065
  · exact MergedCutProfiles.Batch472.valid18890
  · exact MergedCutProfiles.Batch601.valid24066
  · exact MergedCutProfiles.Batch601.valid24067
  · exact MergedCutProfiles.Batch472.valid18901
  · exact MergedCutProfiles.Batch601.valid24068
  · exact MergedCutProfiles.Batch348.valid13945
  · exact MergedCutProfiles.Batch601.valid24069
  · exact MergedCutProfiles.Batch601.valid24070
  · exact MergedCutProfiles.Batch349.valid13961
theorem numericValid3969 : retention3969.NumericValid := by decide +kernel
def certificate3969 : RatCutBinCertificate := ⟨⟨retention3969,(1869853342491414037/1000000000000000000),(69043717129131353/1000000000000000000),(5506235676800618567/500000000000000000),(7378856415501689003879/1000000000000000000),(544033944020845443/250000000000000000)⟩,(999763125067472501/1000000000000000000),(722516421505339853/1000000000000000000),(10663702362430649/250000000000000000),(18783209508286437/1000000000000000000)⟩
theorem valid3969 : certificate3969.Valid := by decide +kernel
theorem sound3969 : certificate3969.Sound := rat_cut_bin_certificate_sound certificate3969 profilesValid3969 numericValid3969 valid3969

def retention3970 : RatCutRetentionCertificate := ⟨(19/500),(39/1000),(576660851000000000/333242582177592760029),(146079609754660809/250000000000000000),4,(5704983294689344881/2560000000000000000),true,MergedCutProfiles.Batch601.profile24061,![MergedCutProfiles.Batch601.profile24061,MergedCutProfiles.Batch601.profile24063,MergedCutProfiles.Batch601.profile24071,MergedCutProfiles.Batch472.profile18890,MergedCutProfiles.Batch601.profile24067,MergedCutProfiles.Batch601.profile24068,MergedCutProfiles.Batch601.profile24069,MergedCutProfiles.Batch349.profile13961,MergedCutProfiles.Batch601.profile24072,MergedCutProfiles.Batch472.profile18881,MergedCutProfiles.Batch472.profile18902,MergedCutProfiles.Batch471.profile18869,MergedCutProfiles.Batch601.profile24073,MergedCutProfiles.Batch601.profile24074,MergedCutProfiles.Batch350.profile14004,MergedCutProfiles.Batch601.profile24075]⟩
theorem profilesValid3970 : retention3970.ProfilesValid := by
  change ∀ j : Fin 16, (retention3970.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch601.valid24061
  · exact MergedCutProfiles.Batch601.valid24063
  · exact MergedCutProfiles.Batch601.valid24071
  · exact MergedCutProfiles.Batch472.valid18890
  · exact MergedCutProfiles.Batch601.valid24067
  · exact MergedCutProfiles.Batch601.valid24068
  · exact MergedCutProfiles.Batch601.valid24069
  · exact MergedCutProfiles.Batch349.valid13961
  · exact MergedCutProfiles.Batch601.valid24072
  · exact MergedCutProfiles.Batch472.valid18881
  · exact MergedCutProfiles.Batch472.valid18902
  · exact MergedCutProfiles.Batch471.valid18869
  · exact MergedCutProfiles.Batch601.valid24073
  · exact MergedCutProfiles.Batch601.valid24074
  · exact MergedCutProfiles.Batch350.valid14004
  · exact MergedCutProfiles.Batch601.valid24075
theorem numericValid3970 : retention3970.NumericValid := by decide +kernel
def certificate3970 : RatCutBinCertificate := ⟨⟨retention3970,(1869853342491414037/1000000000000000000),(69043717129131353/1000000000000000000),(5506235676800618567/500000000000000000),(7378856415501689003879/1000000000000000000),(2181616031457098507/1000000000000000000)⟩,(999763125067472501/1000000000000000000),(357965741640022013/500000000000000000),(1400784774981507/31250000000000000),(19816569906564001/1000000000000000000)⟩
theorem valid3970 : certificate3970.Valid := by decide +kernel
theorem sound3970 : certificate3970.Sound := rat_cut_bin_certificate_sound certificate3970 profilesValid3970 numericValid3970 valid3970

def retention3971 : RatCutRetentionCertificate := ⟨(19/500),(39/1000),(1248935953409920082/333242582177592760029),(576660851/500000000),(11/4),(18736842906257467347/8000000000000000000),true,MergedCutProfiles.Batch601.profile24076,![MergedCutProfiles.Batch601.profile24076,MergedCutProfiles.Batch601.profile24077,MergedCutProfiles.Batch348.profile13945,MergedCutProfiles.Batch601.profile24078,MergedCutProfiles.Batch472.profile18902,MergedCutProfiles.Batch601.profile24073,MergedCutProfiles.Batch350.profile14004,MergedCutProfiles.Batch601.profile24079,MergedCutProfiles.Batch348.profile13947,MergedCutProfiles.Batch471.profile18873,MergedCutProfiles.Batch472.profile18883,MergedCutProfiles.Batch602.profile24080,MergedCutProfiles.Batch349.profile13990,MergedCutProfiles.Batch602.profile24081,MergedCutProfiles.Batch602.profile24082,MergedCutProfiles.Batch602.profile24083]⟩
theorem profilesValid3971 : retention3971.ProfilesValid := by
  change ∀ j : Fin 16, (retention3971.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch601.valid24076
  · exact MergedCutProfiles.Batch601.valid24077
  · exact MergedCutProfiles.Batch348.valid13945
  · exact MergedCutProfiles.Batch601.valid24078
  · exact MergedCutProfiles.Batch472.valid18902
  · exact MergedCutProfiles.Batch601.valid24073
  · exact MergedCutProfiles.Batch350.valid14004
  · exact MergedCutProfiles.Batch601.valid24079
  · exact MergedCutProfiles.Batch348.valid13947
  · exact MergedCutProfiles.Batch471.valid18873
  · exact MergedCutProfiles.Batch472.valid18883
  · exact MergedCutProfiles.Batch602.valid24080
  · exact MergedCutProfiles.Batch349.valid13990
  · exact MergedCutProfiles.Batch602.valid24081
  · exact MergedCutProfiles.Batch602.valid24082
  · exact MergedCutProfiles.Batch602.valid24083
theorem numericValid3971 : retention3971.NumericValid := by decide +kernel
def certificate3971 : RatCutBinCertificate := ⟨⟨retention3971,(1869853342491414037/1000000000000000000),(69043717129131353/1000000000000000000),(5506235676800618567/500000000000000000),(7378856415501689003879/1000000000000000000),(2309866412963747601/1000000000000000000)⟩,(999763125067472501/1000000000000000000),(226957995605434551/500000000000000000),(46890332977588297/250000000000000000),(24904391806288079/200000000000000000)⟩
theorem valid3971 : certificate3971.Valid := by decide +kernel
theorem sound3971 : certificate3971.Sound := rat_cut_bin_certificate_sound certificate3971 profilesValid3971 numericValid3971 valid3971

def certificates : List RatCutBinCertificate := [certificate3960,certificate3961,certificate3962,certificate3963,certificate3964,certificate3965,certificate3966,certificate3967,certificate3968,certificate3969,certificate3970,certificate3971]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound3960,List.forall_mem_cons.mpr ⟨sound3961,List.forall_mem_cons.mpr ⟨sound3962,List.forall_mem_cons.mpr ⟨sound3963,List.forall_mem_cons.mpr ⟨sound3964,List.forall_mem_cons.mpr ⟨sound3965,List.forall_mem_cons.mpr ⟨sound3966,List.forall_mem_cons.mpr ⟨sound3967,List.forall_mem_cons.mpr ⟨sound3968,List.forall_mem_cons.mpr ⟨sound3969,List.forall_mem_cons.mpr ⟨sound3970,List.forall_mem_cons.mpr ⟨sound3971,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch330
