import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch036
import Cycle12.MergedCutProfiles.Batch037
import Cycle12.MergedCutProfiles.Batch327
import Cycle12.MergedCutProfiles.Batch328

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch176

def retention2112 : RatCutRetentionCertificate := ⟨(1/40),(13/500),(14868330521212450049/40079938802876286037),(2374998073712754467/500000000000000000),(6/5),(149492569447113144579080438092074247791/118749903685637723350000000000000000000),false,MergedCutProfiles.Batch327.profile13108,(fun _ => MergedCutProfiles.Batch327.profile13108)⟩
theorem profilesValid2112 : retention2112.ProfilesValid := by
  exact MergedCutProfiles.Batch327.valid13108
theorem numericValid2112 : retention2112.NumericValid := by decide +kernel
def certificate2112 : RatCutBinCertificate := ⟨⟨retention2112,(48534072011850779/25000000000000000),(14531335098101001/500000000000000000),(2284636561984684481/250000000000000000),(18404084515066028601/12500000000000000),(625738508194559499/500000000000000000)⟩,(499358340259840289/500000000000000000),(430219054721423521/1000000000000000000),(41381504550395751/200000000000000000),(11384747568953439/62500000000000000)⟩
theorem valid2112 : certificate2112.Valid := by decide +kernel
theorem sound2112 : certificate2112.Sound := rat_cut_bin_certificate_sound certificate2112 profilesValid2112 numericValid2112 valid2112

def retention2113 : RatCutRetentionCertificate := ⟨(1/40),(13/500),(16000000000000000000/40079938802876286037),(14868330521212450049/250000000000000000),1,(71345753101838839071218421402933793807/59473322084849800196000000000000000000),false,MergedCutProfiles.Batch327.profile13109,(fun _ => MergedCutProfiles.Batch327.profile13109)⟩
theorem profilesValid2113 : retention2113.ProfilesValid := by
  exact MergedCutProfiles.Batch327.valid13109
theorem numericValid2113 : retention2113.NumericValid := by decide +kernel
def certificate2113 : RatCutBinCertificate := ⟨⟨retention2113,(48534072011850779/25000000000000000),(14531335098101001/500000000000000000),(2284636561984684481/250000000000000000),(18404084515066028601/12500000000000000),(1193452181128601187/1000000000000000000)⟩,(499358340259840289/500000000000000000),(190166916406821487/500000000000000000),(5039855724422091/20000000000000000),(294443329106854509/1000000000000000000)⟩
theorem valid2113 : certificate2113.Valid := by decide +kernel
theorem sound2113 : certificate2113.Sound := rat_cut_bin_certificate_sound certificate2113 profilesValid2113 numericValid2113 valid2113

def retention2114 : RatCutRetentionCertificate := ⟨(1/40),(13/500),(1/2),64,1,(255373741328073457130936126923517436199/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch036.profile1465,(fun _ => MergedCutProfiles.Batch036.profile1465)⟩
theorem profilesValid2114 : retention2114.ProfilesValid := by
  exact MergedCutProfiles.Batch036.valid1465
theorem numericValid2114 : retention2114.NumericValid := by decide +kernel
def certificate2114 : RatCutBinCertificate := ⟨⟨retention2114,(48534072011850779/25000000000000000),(14531335098101001/500000000000000000),(2284636561984684481/250000000000000000),(18404084515066028601/12500000000000000),(495689848270723319/500000000000000000)⟩,(499358340259840289/500000000000000000),(457333832093823431/1000000000000000000),(92437317670040999/500000000000000000),(45062906925976701/250000000000000000)⟩
theorem valid2114 : certificate2114.Valid := by decide +kernel
theorem sound2114 : certificate2114.Sound := rat_cut_bin_certificate_sound certificate2114 profilesValid2114 numericValid2114 valid2114

def retention2115 : RatCutRetentionCertificate := ⟨(1/40),(13/500),(16000000000000000000/40079938802876286037),(5316065545981350163/1000000000000000000),(11/10),(2518466212093030270235959232269812867391/2126426218392540065200000000000000000000),false,MergedCutProfiles.Batch327.profile13109,(fun _ => MergedCutProfiles.Batch327.profile13109)⟩
theorem profilesValid2115 : retention2115.ProfilesValid := by
  exact MergedCutProfiles.Batch327.valid13109
theorem numericValid2115 : retention2115.NumericValid := by decide +kernel
def certificate2115 : RatCutBinCertificate := ⟨⟨retention2115,(56003534536850779/25000000000000000),(14531335098101001/500000000000000000),(2284636561984684481/250000000000000000),(18404084515066028601/12500000000000000),(588264532119007651/500000000000000000)⟩,(249629791946886493/250000000000000000),(204568260678907703/1000000000000000000),(29409162487499419/62500000000000000),(212395347851864113/500000000000000000)⟩
theorem valid2115 : certificate2115.Valid := by decide +kernel
theorem sound2115 : certificate2115.Sound := rat_cut_bin_certificate_sound certificate2115 profilesValid2115 numericValid2115 valid2115

def retention2116 : RatCutRetentionCertificate := ⟨(1/40),(13/500),(1/2),64,1,(255373741328073457130936126923517436199/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch036.profile1465,(fun _ => MergedCutProfiles.Batch036.profile1465)⟩
theorem profilesValid2116 : retention2116.ProfilesValid := by
  exact MergedCutProfiles.Batch036.valid1465
theorem numericValid2116 : retention2116.NumericValid := by decide +kernel
def certificate2116 : RatCutBinCertificate := ⟨⟨retention2116,(56003534536850779/25000000000000000),(14531335098101001/500000000000000000),(2284636561984684481/250000000000000000),(18404084515066028601/12500000000000000),(990429512181828699/1000000000000000000)⟩,(249629791946886493/250000000000000000),(121503096055344603/500000000000000000),(82623843408844843/200000000000000000),(402328933323402819/1000000000000000000)⟩
theorem valid2116 : certificate2116.Valid := by decide +kernel
theorem sound2116 : certificate2116.Sound := rat_cut_bin_certificate_sound certificate2116 profilesValid2116 numericValid2116 valid2116

def retention2117 : RatCutRetentionCertificate := ⟨(13/500),(27/1000),(676556418166945703/147929067133845158561),(669857839769253171/1000000000000000000),4,(118083267812048914239/51200000000000000000),true,MergedCutProfiles.Batch327.profile13110,![MergedCutProfiles.Batch327.profile13110,MergedCutProfiles.Batch327.profile13111,MergedCutProfiles.Batch327.profile13112,MergedCutProfiles.Batch327.profile13113,MergedCutProfiles.Batch327.profile13114,MergedCutProfiles.Batch327.profile13115,MergedCutProfiles.Batch327.profile13116,MergedCutProfiles.Batch327.profile13117,MergedCutProfiles.Batch327.profile13118,MergedCutProfiles.Batch327.profile13119,MergedCutProfiles.Batch328.profile13120,MergedCutProfiles.Batch328.profile13121,MergedCutProfiles.Batch037.profile1488,MergedCutProfiles.Batch328.profile13122,MergedCutProfiles.Batch328.profile13123,MergedCutProfiles.Batch037.profile1503]⟩
theorem profilesValid2117 : retention2117.ProfilesValid := by
  change ∀ j : Fin 16, (retention2117.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch327.valid13110
  · exact MergedCutProfiles.Batch327.valid13111
  · exact MergedCutProfiles.Batch327.valid13112
  · exact MergedCutProfiles.Batch327.valid13113
  · exact MergedCutProfiles.Batch327.valid13114
  · exact MergedCutProfiles.Batch327.valid13115
  · exact MergedCutProfiles.Batch327.valid13116
  · exact MergedCutProfiles.Batch327.valid13117
  · exact MergedCutProfiles.Batch327.valid13118
  · exact MergedCutProfiles.Batch327.valid13119
  · exact MergedCutProfiles.Batch328.valid13120
  · exact MergedCutProfiles.Batch328.valid13121
  · exact MergedCutProfiles.Batch037.valid1488
  · exact MergedCutProfiles.Batch328.valid13122
  · exact MergedCutProfiles.Batch328.valid13123
  · exact MergedCutProfiles.Batch037.valid1503
theorem numericValid2117 : retention2117.NumericValid := by decide +kernel
def certificate2117 : RatCutBinCertificate := ⟨⟨retention2117,(969347232330873023/500000000000000000),(31463473579235007/1000000000000000000),(4632319182169648791/500000000000000000),(1377319449894569306277/1000000000000000000),(71249304273572669/31250000000000000)⟩,(199726653376095357/200000000000000000),(240186254817606153/500000000000000000),(167421429115281583/1000000000000000000),(78563982241024593/1000000000000000000)⟩
theorem valid2117 : certificate2117.Valid := by decide +kernel
theorem sound2117 : certificate2117.Sound := rat_cut_bin_certificate_sound certificate2117 profilesValid2117 numericValid2117 valid2117

def retention2118 : RatCutRetentionCertificate := ⟨(13/500),(27/1000),(939527190065619275/147929067133845158561),(676556418166945703/1000000000000000000),(79/20),(2929724263307345166679/1280000000000000000000),true,MergedCutProfiles.Batch328.profile13124,![MergedCutProfiles.Batch328.profile13124,MergedCutProfiles.Batch328.profile13125,MergedCutProfiles.Batch036.profile1469,MergedCutProfiles.Batch328.profile13126,MergedCutProfiles.Batch327.profile13116,MergedCutProfiles.Batch036.profile1471,MergedCutProfiles.Batch037.profile1502,MergedCutProfiles.Batch328.profile13127,MergedCutProfiles.Batch036.profile1473,MergedCutProfiles.Batch328.profile13122,MergedCutProfiles.Batch037.profile1489,MergedCutProfiles.Batch036.profile1475,MergedCutProfiles.Batch328.profile13128,MergedCutProfiles.Batch037.profile1515,MergedCutProfiles.Batch036.profile1477,MergedCutProfiles.Batch328.profile13129]⟩
theorem profilesValid2118 : retention2118.ProfilesValid := by
  change ∀ j : Fin 16, (retention2118.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch328.valid13124
  · exact MergedCutProfiles.Batch328.valid13125
  · exact MergedCutProfiles.Batch036.valid1469
  · exact MergedCutProfiles.Batch328.valid13126
  · exact MergedCutProfiles.Batch327.valid13116
  · exact MergedCutProfiles.Batch036.valid1471
  · exact MergedCutProfiles.Batch037.valid1502
  · exact MergedCutProfiles.Batch328.valid13127
  · exact MergedCutProfiles.Batch036.valid1473
  · exact MergedCutProfiles.Batch328.valid13122
  · exact MergedCutProfiles.Batch037.valid1489
  · exact MergedCutProfiles.Batch036.valid1475
  · exact MergedCutProfiles.Batch328.valid13128
  · exact MergedCutProfiles.Batch037.valid1515
  · exact MergedCutProfiles.Batch036.valid1477
  · exact MergedCutProfiles.Batch328.valid13129
theorem numericValid2118 : retention2118.NumericValid := by decide +kernel
def certificate2118 : RatCutBinCertificate := ⟨⟨retention2118,(969347232330873023/500000000000000000),(31463473579235007/1000000000000000000),(4632319182169648791/500000000000000000),(1377319449894569306277/1000000000000000000),(452568038704359261/200000000000000000)⟩,(199726653376095357/200000000000000000),(240593092741563743/500000000000000000),(2606649044631999/15625000000000000),(19643345854616143/250000000000000000)⟩
theorem valid2118 : certificate2118.Valid := by decide +kernel
theorem sound2118 : certificate2118.Sound := rat_cut_bin_certificate_sound certificate2118 profilesValid2118 numericValid2118 valid2118

def retention2119 : RatCutRetentionCertificate := ⟨(13/500),(27/1000),(1152034725000000000/147929067133845158561),(37581087602624771/40000000000000000),3,(579834922093876304963/256000000000000000000),true,MergedCutProfiles.Batch328.profile13130,![MergedCutProfiles.Batch328.profile13130,MergedCutProfiles.Batch328.profile13131,MergedCutProfiles.Batch037.profile1485,MergedCutProfiles.Batch328.profile13132,MergedCutProfiles.Batch328.profile13133,MergedCutProfiles.Batch037.profile1487,MergedCutProfiles.Batch328.profile13121,MergedCutProfiles.Batch328.profile13134,MergedCutProfiles.Batch037.profile1489,MergedCutProfiles.Batch328.profile13135,MergedCutProfiles.Batch036.profile1476,MergedCutProfiles.Batch037.profile1491,MergedCutProfiles.Batch328.profile13136,MergedCutProfiles.Batch328.profile13137,MergedCutProfiles.Batch328.profile13138,MergedCutProfiles.Batch037.profile1480]⟩
theorem profilesValid2119 : retention2119.ProfilesValid := by
  change ∀ j : Fin 16, (retention2119.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch328.valid13130
  · exact MergedCutProfiles.Batch328.valid13131
  · exact MergedCutProfiles.Batch037.valid1485
  · exact MergedCutProfiles.Batch328.valid13132
  · exact MergedCutProfiles.Batch328.valid13133
  · exact MergedCutProfiles.Batch037.valid1487
  · exact MergedCutProfiles.Batch328.valid13121
  · exact MergedCutProfiles.Batch328.valid13134
  · exact MergedCutProfiles.Batch037.valid1489
  · exact MergedCutProfiles.Batch328.valid13135
  · exact MergedCutProfiles.Batch036.valid1476
  · exact MergedCutProfiles.Batch037.valid1491
  · exact MergedCutProfiles.Batch328.valid13136
  · exact MergedCutProfiles.Batch328.valid13137
  · exact MergedCutProfiles.Batch328.valid13138
  · exact MergedCutProfiles.Batch037.valid1480
theorem numericValid2119 : retention2119.NumericValid := by decide +kernel
def certificate2119 : RatCutBinCertificate := ⟨⟨retention2119,(969347232330873023/500000000000000000),(31463473579235007/1000000000000000000),(4632319182169648791/500000000000000000),(1377319449894569306277/1000000000000000000),(2245228106968032287/1000000000000000000)⟩,(199726653376095357/200000000000000000),(405286260415001753/1000000000000000000),(5716839726844929/25000000000000000),(27004028564927567/200000000000000000)⟩
theorem valid2119 : certificate2119.Valid := by decide +kernel
theorem sound2119 : certificate2119.Sound := rat_cut_bin_certificate_sound certificate2119 profilesValid2119 numericValid2119 valid2119

def retention2120 : RatCutRetentionCertificate := ⟨(13/500),(27/1000),(1169444394141894231/147929067133845158561),(46081389/40000000),(51/20),(7213689385856816771/3200000000000000000),true,MergedCutProfiles.Batch328.profile13130,![MergedCutProfiles.Batch328.profile13130,MergedCutProfiles.Batch328.profile13139,MergedCutProfiles.Batch037.profile1485,MergedCutProfiles.Batch327.profile13116,MergedCutProfiles.Batch328.profile13133,MergedCutProfiles.Batch036.profile1472,MergedCutProfiles.Batch328.profile13140,MergedCutProfiles.Batch328.profile13141,MergedCutProfiles.Batch037.profile1514,MergedCutProfiles.Batch328.profile13142,MergedCutProfiles.Batch328.profile13143,MergedCutProfiles.Batch328.profile13144,MergedCutProfiles.Batch037.profile1505,MergedCutProfiles.Batch328.profile13145,MergedCutProfiles.Batch328.profile13146,MergedCutProfiles.Batch328.profile13147]⟩
theorem profilesValid2120 : retention2120.ProfilesValid := by
  change ∀ j : Fin 16, (retention2120.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch328.valid13130
  · exact MergedCutProfiles.Batch328.valid13139
  · exact MergedCutProfiles.Batch037.valid1485
  · exact MergedCutProfiles.Batch327.valid13116
  · exact MergedCutProfiles.Batch328.valid13133
  · exact MergedCutProfiles.Batch036.valid1472
  · exact MergedCutProfiles.Batch328.valid13140
  · exact MergedCutProfiles.Batch328.valid13141
  · exact MergedCutProfiles.Batch037.valid1514
  · exact MergedCutProfiles.Batch328.valid13142
  · exact MergedCutProfiles.Batch328.valid13143
  · exact MergedCutProfiles.Batch328.valid13144
  · exact MergedCutProfiles.Batch037.valid1505
  · exact MergedCutProfiles.Batch328.valid13145
  · exact MergedCutProfiles.Batch328.valid13146
  · exact MergedCutProfiles.Batch328.valid13147
theorem numericValid2120 : retention2120.NumericValid := by decide +kernel
def certificate2120 : RatCutBinCertificate := ⟨⟨retention2120,(969347232330873023/500000000000000000),(31463473579235007/1000000000000000000),(4632319182169648791/500000000000000000),(1377319449894569306277/1000000000000000000),(223748868975522851/100000000000000000)⟩,(199726653376095357/200000000000000000),(46093225063531541/125000000000000000),(263372382556673919/1000000000000000000),(44416815037327071/250000000000000000)⟩
theorem valid2120 : certificate2120.Valid := by decide +kernel
theorem sound2120 : certificate2120.Sound := rat_cut_bin_certificate_sound certificate2120 profilesValid2120 numericValid2120 valid2120

def retention2121 : RatCutRetentionCertificate := ⟨(13/500),(27/1000),(1607916668785843771/147929067133845158561),(1169444394141894231/1000000000000000000),(5/2),(570824136358885846311/256000000000000000000),true,MergedCutProfiles.Batch328.profile13148,![MergedCutProfiles.Batch328.profile13148,MergedCutProfiles.Batch328.profile13149,MergedCutProfiles.Batch328.profile13150,MergedCutProfiles.Batch328.profile13151,MergedCutProfiles.Batch328.profile13121,MergedCutProfiles.Batch328.profile13152,MergedCutProfiles.Batch036.profile1475,MergedCutProfiles.Batch328.profile13143,MergedCutProfiles.Batch328.profile13153,MergedCutProfiles.Batch328.profile13154,MergedCutProfiles.Batch328.profile13155,MergedCutProfiles.Batch037.profile1494,MergedCutProfiles.Batch037.profile1495,MergedCutProfiles.Batch037.profile1483,MergedCutProfiles.Batch328.profile13156,MergedCutProfiles.Batch328.profile13157]⟩
theorem profilesValid2121 : retention2121.ProfilesValid := by
  change ∀ j : Fin 16, (retention2121.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch328.valid13148
  · exact MergedCutProfiles.Batch328.valid13149
  · exact MergedCutProfiles.Batch328.valid13150
  · exact MergedCutProfiles.Batch328.valid13151
  · exact MergedCutProfiles.Batch328.valid13121
  · exact MergedCutProfiles.Batch328.valid13152
  · exact MergedCutProfiles.Batch036.valid1475
  · exact MergedCutProfiles.Batch328.valid13143
  · exact MergedCutProfiles.Batch328.valid13153
  · exact MergedCutProfiles.Batch328.valid13154
  · exact MergedCutProfiles.Batch328.valid13155
  · exact MergedCutProfiles.Batch037.valid1494
  · exact MergedCutProfiles.Batch037.valid1495
  · exact MergedCutProfiles.Batch037.valid1483
  · exact MergedCutProfiles.Batch328.valid13156
  · exact MergedCutProfiles.Batch328.valid13157
theorem numericValid2121 : retention2121.NumericValid := by decide +kernel
def certificate2121 : RatCutBinCertificate := ⟨⟨retention2121,(969347232330873023/500000000000000000),(31463473579235007/1000000000000000000),(4632319182169648791/500000000000000000),(1377319449894569306277/1000000000000000000),(1106660869780033941/500000000000000000)⟩,(199726653376095357/200000000000000000),(11570235021721363/31250000000000000),(8183668545736481/31250000000000000),(88840006342762361/500000000000000000)⟩
theorem valid2121 : certificate2121.Valid := by decide +kernel
theorem sound2121 : certificate2121.Sound := rat_cut_bin_certificate_sound certificate2121 profilesValid2121 numericValid2121 valid2121

def retention2122 : RatCutRetentionCertificate := ⟨(13/500),(27/1000),(15236808606933842692/147929067133845158561),(1607916668785843771/1000000000000000000),(41/20),(4854118753838479759834106948152294063399/2572666670057350033600000000000000000000),false,MergedCutProfiles.Batch328.profile13158,(fun _ => MergedCutProfiles.Batch328.profile13158)⟩
theorem profilesValid2122 : retention2122.ProfilesValid := by
  exact MergedCutProfiles.Batch328.valid13158
theorem numericValid2122 : retention2122.NumericValid := by decide +kernel
def certificate2122 : RatCutBinCertificate := ⟨⟨retention2122,(969347232330873023/500000000000000000),(31463473579235007/1000000000000000000),(4632319182169648791/500000000000000000),(1377319449894569306277/1000000000000000000),(468326790360750393/250000000000000000)⟩,(199726653376095357/200000000000000000),(76725068987290241/200000000000000000),(12441264404214179/50000000000000000),(177750060865158211/1000000000000000000)⟩
theorem valid2122 : certificate2122.Valid := by decide +kernel
theorem sound2122 : certificate2122.Sound := rat_cut_bin_certificate_sound certificate2122 profilesValid2122 numericValid2122 valid2122

def retention2123 : RatCutRetentionCertificate := ⟨(13/500),(27/1000),(64000000000000000000/147929067133845158561),(3809202151733460673/250000000000000000),1,(1062919205705429381044809016077305073/952300537933365168250000000000000000),false,MergedCutProfiles.Batch328.profile13159,(fun _ => MergedCutProfiles.Batch328.profile13159)⟩
theorem profilesValid2123 : retention2123.ProfilesValid := by
  exact MergedCutProfiles.Batch328.valid13159
theorem numericValid2123 : retention2123.NumericValid := by decide +kernel
def certificate2123 : RatCutBinCertificate := ⟨⟨retention2123,(969347232330873023/500000000000000000),(31463473579235007/1000000000000000000),(4632319182169648791/500000000000000000),(1377319449894569306277/1000000000000000000),(554787716718453371/500000000000000000)⟩,(199726653376095357/200000000000000000),(86178449218032693/200000000000000000),(51585062447535053/250000000000000000),(213107731269922081/1000000000000000000)⟩
theorem valid2123 : certificate2123.Valid := by decide +kernel
theorem sound2123 : certificate2123.Sound := rat_cut_bin_certificate_sound certificate2123 profilesValid2123 numericValid2123 valid2123

def certificates : List RatCutBinCertificate := [certificate2112,certificate2113,certificate2114,certificate2115,certificate2116,certificate2117,certificate2118,certificate2119,certificate2120,certificate2121,certificate2122,certificate2123]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound2112,List.forall_mem_cons.mpr ⟨sound2113,List.forall_mem_cons.mpr ⟨sound2114,List.forall_mem_cons.mpr ⟨sound2115,List.forall_mem_cons.mpr ⟨sound2116,List.forall_mem_cons.mpr ⟨sound2117,List.forall_mem_cons.mpr ⟨sound2118,List.forall_mem_cons.mpr ⟨sound2119,List.forall_mem_cons.mpr ⟨sound2120,List.forall_mem_cons.mpr ⟨sound2121,List.forall_mem_cons.mpr ⟨sound2122,List.forall_mem_cons.mpr ⟨sound2123,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch176
