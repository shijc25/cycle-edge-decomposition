import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch038
import Cycle12.MergedCutProfiles.Batch039
import Cycle12.MergedCutProfiles.Batch040
import Cycle12.MergedCutProfiles.Batch328
import Cycle12.MergedCutProfiles.Batch329
import Cycle12.MergedCutProfiles.Batch330

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch177

def retention2124 : RatCutRetentionCertificate := ⟨(13/500),(27/1000),(1/2),64,1,(15960890419747252013481485060871619639/16000000000000000000000000000000000000),false,MergedCutProfiles.Batch038.profile1543,(fun _ => MergedCutProfiles.Batch038.profile1543)⟩
theorem profilesValid2124 : retention2124.ProfilesValid := by
  exact MergedCutProfiles.Batch038.valid1543
theorem numericValid2124 : retention2124.NumericValid := by decide +kernel
def certificate2124 : RatCutBinCertificate := ⟨⟨retention2124,(969347232330873023/500000000000000000),(31463473579235007/1000000000000000000),(4632319182169648791/500000000000000000),(1377319449894569306277/1000000000000000000),(990971683092028327/1000000000000000000)⟩,(199726653376095357/200000000000000000),(460643903360057751/1000000000000000000),(91148500702012323/500000000000000000),(35530287984729757/200000000000000000)⟩
theorem valid2124 : certificate2124.Valid := by decide +kernel
theorem sound2124 : certificate2124.Sound := rat_cut_bin_certificate_sound certificate2124 profilesValid2124 numericValid2124 valid2124

def retention2125 : RatCutRetentionCertificate := ⟨(13/500),(27/1000),(61726801059972058552/147929067133845158561),(5391842453161152089/1000000000000000000),(11/10),(2480991058843964270850450093602909777759/2156736981264460835600000000000000000000),false,MergedCutProfiles.Batch329.profile13160,(fun _ => MergedCutProfiles.Batch329.profile13160)⟩
theorem profilesValid2125 : retention2125.ProfilesValid := by
  exact MergedCutProfiles.Batch329.valid13160
theorem numericValid2125 : retention2125.NumericValid := by decide +kernel
def certificate2125 : RatCutBinCertificate := ⟨⟨retention2125,(1122796747330873023/500000000000000000),(31463473579235007/1000000000000000000),(4632319182169648791/500000000000000000),(1377319449894569306277/1000000000000000000),(1141955873374728767/1000000000000000000)⟩,(199683380033923329/200000000000000000),(52298034342567679/250000000000000000),(463289711498791751/1000000000000000000),(204311778234400077/500000000000000000)⟩
theorem valid2125 : certificate2125.Valid := by decide +kernel
theorem sound2125 : certificate2125.Sound := rat_cut_bin_certificate_sound certificate2125 profilesValid2125 numericValid2125 valid2125

def retention2126 : RatCutRetentionCertificate := ⟨(13/500),(27/1000),(64000000000000000000/147929067133845158561),(7715850132496507319/125000000000000000),1,(4367733136826572440445314374257966083/3857925066248253659500000000000000000),false,MergedCutProfiles.Batch328.profile13159,(fun _ => MergedCutProfiles.Batch328.profile13159)⟩
theorem profilesValid2126 : retention2126.ProfilesValid := by
  exact MergedCutProfiles.Batch328.valid13159
theorem numericValid2126 : retention2126.NumericValid := by decide +kernel
def certificate2126 : RatCutBinCertificate := ⟨⟨retention2126,(1122796747330873023/500000000000000000),(31463473579235007/1000000000000000000),(4632319182169648791/500000000000000000),(1377319449894569306277/1000000000000000000),(281129860329159877/250000000000000000)⟩,(199683380033923329/200000000000000000),(26554475311481983/125000000000000000),(458258288013296939/1000000000000000000),(101058627838278407/200000000000000000)⟩
theorem valid2126 : certificate2126.Valid := by decide +kernel
theorem sound2126 : certificate2126.Sound := rat_cut_bin_certificate_sound certificate2126 profilesValid2126 numericValid2126 valid2126

def retention2127 : RatCutRetentionCertificate := ⟨(13/500),(27/1000),(1/2),64,1,(15960890419747252013481485060871619639/16000000000000000000000000000000000000),false,MergedCutProfiles.Batch038.profile1543,(fun _ => MergedCutProfiles.Batch038.profile1543)⟩
theorem profilesValid2127 : retention2127.ProfilesValid := by
  exact MergedCutProfiles.Batch038.valid1543
theorem numericValid2127 : retention2127.NumericValid := by decide +kernel
def certificate2127 : RatCutBinCertificate := ⟨⟨retention2127,(1122796747330873023/500000000000000000),(31463473579235007/1000000000000000000),(4632319182169648791/500000000000000000),(1377319449894569306277/1000000000000000000),(98992942838236889/100000000000000000)⟩,(199683380033923329/200000000000000000),(120659202103001367/500000000000000000),(415508317902600203/1000000000000000000),(202206346216421013/500000000000000000)⟩
theorem valid2127 : certificate2127.Valid := by decide +kernel
theorem sound2127 : certificate2127.Sound := rat_cut_bin_certificate_sound certificate2127 profilesValid2127 numericValid2127 valid2127

def retention2128 : RatCutRetentionCertificate := ⟨(27/1000),(7/250),(341999026683979690/68433625112009156493),(42326612213363823/62500000000000000),(79/20),(23013497914395659493/10000000000000000000),true,MergedCutProfiles.Batch329.profile13161,![MergedCutProfiles.Batch329.profile13161,MergedCutProfiles.Batch329.profile13162,MergedCutProfiles.Batch329.profile13163,MergedCutProfiles.Batch329.profile13164,MergedCutProfiles.Batch329.profile13165,MergedCutProfiles.Batch329.profile13166,MergedCutProfiles.Batch329.profile13167,MergedCutProfiles.Batch329.profile13168,MergedCutProfiles.Batch329.profile13169,MergedCutProfiles.Batch329.profile13170,MergedCutProfiles.Batch329.profile13171,MergedCutProfiles.Batch329.profile13172,MergedCutProfiles.Batch329.profile13173,MergedCutProfiles.Batch329.profile13174,MergedCutProfiles.Batch329.profile13175,MergedCutProfiles.Batch329.profile13176]⟩
theorem profilesValid2128 : retention2128.ProfilesValid := by
  change ∀ j : Fin 16, (retention2128.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch329.valid13161
  · exact MergedCutProfiles.Batch329.valid13162
  · exact MergedCutProfiles.Batch329.valid13163
  · exact MergedCutProfiles.Batch329.valid13164
  · exact MergedCutProfiles.Batch329.valid13165
  · exact MergedCutProfiles.Batch329.valid13166
  · exact MergedCutProfiles.Batch329.valid13167
  · exact MergedCutProfiles.Batch329.valid13168
  · exact MergedCutProfiles.Batch329.valid13169
  · exact MergedCutProfiles.Batch329.valid13170
  · exact MergedCutProfiles.Batch329.valid13171
  · exact MergedCutProfiles.Batch329.valid13172
  · exact MergedCutProfiles.Batch329.valid13173
  · exact MergedCutProfiles.Batch329.valid13174
  · exact MergedCutProfiles.Batch329.valid13175
  · exact MergedCutProfiles.Batch329.valid13176
theorem numericValid2128 : retention2128.NumericValid := by decide +kernel
def certificate2128 : RatCutBinCertificate := ⟨⟨retention2128,(1955981423753964107/1000000000000000000),(1358828718451041/40000000000000000),(29354444920045191/3125000000000000),(161509788327666181233/125000000000000000),(2273408468500336743/1000000000000000000)⟩,(24963343358780261/25000000000000000),(474139398345502997/1000000000000000000),(34406419294978893/200000000000000000),(81341871686566713/1000000000000000000)⟩
theorem valid2128 : certificate2128.Valid := by decide +kernel
theorem sound2128 : certificate2128.Sound := rat_cut_bin_certificate_sound certificate2128 profilesValid2128 numericValid2128 valid2128

def retention2129 : RatCutRetentionCertificate := ⟨(27/1000),(7/250),(921926034321822979/136867250224018312986),(34199902668397969/50000000000000000),(79/20),(146613702977586456837/64000000000000000000),true,MergedCutProfiles.Batch329.profile13177,![MergedCutProfiles.Batch329.profile13177,MergedCutProfiles.Batch329.profile13178,MergedCutProfiles.Batch329.profile13164,MergedCutProfiles.Batch329.profile13179,MergedCutProfiles.Batch329.profile13180,MergedCutProfiles.Batch329.profile13168,MergedCutProfiles.Batch039.profile1578,MergedCutProfiles.Batch329.profile13181,MergedCutProfiles.Batch329.profile13182,MergedCutProfiles.Batch329.profile13183,MergedCutProfiles.Batch329.profile13184,MergedCutProfiles.Batch329.profile13185,MergedCutProfiles.Batch329.profile13186,MergedCutProfiles.Batch039.profile1580,MergedCutProfiles.Batch329.profile13187,MergedCutProfiles.Batch329.profile13188]⟩
theorem profilesValid2129 : retention2129.ProfilesValid := by
  change ∀ j : Fin 16, (retention2129.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch329.valid13177
  · exact MergedCutProfiles.Batch329.valid13178
  · exact MergedCutProfiles.Batch329.valid13164
  · exact MergedCutProfiles.Batch329.valid13179
  · exact MergedCutProfiles.Batch329.valid13180
  · exact MergedCutProfiles.Batch329.valid13168
  · exact MergedCutProfiles.Batch039.valid1578
  · exact MergedCutProfiles.Batch329.valid13181
  · exact MergedCutProfiles.Batch329.valid13182
  · exact MergedCutProfiles.Batch329.valid13183
  · exact MergedCutProfiles.Batch329.valid13184
  · exact MergedCutProfiles.Batch329.valid13185
  · exact MergedCutProfiles.Batch329.valid13186
  · exact MergedCutProfiles.Batch039.valid1580
  · exact MergedCutProfiles.Batch329.valid13187
  · exact MergedCutProfiles.Batch329.valid13188
theorem numericValid2129 : retention2129.NumericValid := by decide +kernel
def certificate2129 : RatCutBinCertificate := ⟨⟨retention2129,(1955981423753964107/1000000000000000000),(1358828718451041/40000000000000000),(29354444920045191/3125000000000000),(161509788327666181233/125000000000000000),(1131448894402271509/500000000000000000)⟩,(24963343358780261/25000000000000000),(473590722222721091/1000000000000000000),(86220931707889177/500000000000000000),(81367393933608469/1000000000000000000)⟩
theorem valid2129 : certificate2129.Valid := by decide +kernel
theorem sound2129 : certificate2129.Sound := rat_cut_bin_certificate_sound certificate2129 profilesValid2129 numericValid2129 valid2129

def retention2130 : RatCutRetentionCertificate := ⟨(27/1000),(7/250),(14912719500000000/1754708336205362987),(921926034321822979/1000000000000000000),(61/20),(2896223982164992963083/1280000000000000000000),true,MergedCutProfiles.Batch329.profile13189,![MergedCutProfiles.Batch329.profile13189,MergedCutProfiles.Batch329.profile13190,MergedCutProfiles.Batch039.profile1563,MergedCutProfiles.Batch329.profile13191,MergedCutProfiles.Batch329.profile13192,MergedCutProfiles.Batch039.profile1565,MergedCutProfiles.Batch329.profile13193,MergedCutProfiles.Batch329.profile13194,MergedCutProfiles.Batch039.profile1567,MergedCutProfiles.Batch329.profile13195,MergedCutProfiles.Batch038.profile1554,MergedCutProfiles.Batch039.profile1569,MergedCutProfiles.Batch329.profile13196,MergedCutProfiles.Batch329.profile13197,MergedCutProfiles.Batch039.profile1570,MergedCutProfiles.Batch038.profile1558]⟩
theorem profilesValid2130 : retention2130.ProfilesValid := by
  change ∀ j : Fin 16, (retention2130.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch329.valid13189
  · exact MergedCutProfiles.Batch329.valid13190
  · exact MergedCutProfiles.Batch039.valid1563
  · exact MergedCutProfiles.Batch329.valid13191
  · exact MergedCutProfiles.Batch329.valid13192
  · exact MergedCutProfiles.Batch039.valid1565
  · exact MergedCutProfiles.Batch329.valid13193
  · exact MergedCutProfiles.Batch329.valid13194
  · exact MergedCutProfiles.Batch039.valid1567
  · exact MergedCutProfiles.Batch329.valid13195
  · exact MergedCutProfiles.Batch038.valid1554
  · exact MergedCutProfiles.Batch039.valid1569
  · exact MergedCutProfiles.Batch329.valid13196
  · exact MergedCutProfiles.Batch329.valid13197
  · exact MergedCutProfiles.Batch039.valid1570
  · exact MergedCutProfiles.Batch038.valid1558
theorem numericValid2130 : retention2130.NumericValid := by decide +kernel
def certificate2130 : RatCutBinCertificate := ⟨⟨retention2130,(1955981423753964107/1000000000000000000),(1358828718451041/40000000000000000),(29354444920045191/3125000000000000),(161509788327666181233/125000000000000000),(280137506353051211/125000000000000000)⟩,(24963343358780261/25000000000000000),(406510713150530867/1000000000000000000),(113784800076541039/500000000000000000),(132347724046984121/1000000000000000000)⟩
theorem valid2130 : certificate2130.Valid := by decide +kernel
theorem sound2130 : certificate2130.Sound := rat_cut_bin_certificate_sound certificate2130 profilesValid2130 numericValid2130 valid2130

def retention2131 : RatCutRetentionCertificate := ⟨(27/1000),(7/250),(510463727455441667/45622416741339437662),(1163192121/1000000000),(5/2),(35627059904052504901/16000000000000000000),true,MergedCutProfiles.Batch329.profile13198,![MergedCutProfiles.Batch329.profile13198,MergedCutProfiles.Batch329.profile13199,MergedCutProfiles.Batch329.profile13180,MergedCutProfiles.Batch329.profile13169,MergedCutProfiles.Batch330.profile13200,MergedCutProfiles.Batch329.profile13183,MergedCutProfiles.Batch039.profile1579,MergedCutProfiles.Batch330.profile13201,MergedCutProfiles.Batch329.profile13187,MergedCutProfiles.Batch330.profile13202,MergedCutProfiles.Batch330.profile13203,MergedCutProfiles.Batch330.profile13204,MergedCutProfiles.Batch038.profile1559,MergedCutProfiles.Batch039.profile1560,MergedCutProfiles.Batch039.profile1561,MergedCutProfiles.Batch039.profile1574]⟩
theorem profilesValid2131 : retention2131.ProfilesValid := by
  change ∀ j : Fin 16, (retention2131.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch329.valid13198
  · exact MergedCutProfiles.Batch329.valid13199
  · exact MergedCutProfiles.Batch329.valid13180
  · exact MergedCutProfiles.Batch329.valid13169
  · exact MergedCutProfiles.Batch330.valid13200
  · exact MergedCutProfiles.Batch329.valid13183
  · exact MergedCutProfiles.Batch039.valid1579
  · exact MergedCutProfiles.Batch330.valid13201
  · exact MergedCutProfiles.Batch329.valid13187
  · exact MergedCutProfiles.Batch330.valid13202
  · exact MergedCutProfiles.Batch330.valid13203
  · exact MergedCutProfiles.Batch330.valid13204
  · exact MergedCutProfiles.Batch038.valid1559
  · exact MergedCutProfiles.Batch039.valid1560
  · exact MergedCutProfiles.Batch039.valid1561
  · exact MergedCutProfiles.Batch039.valid1574
theorem numericValid2131 : retention2131.NumericValid := by decide +kernel
def certificate2131 : RatCutBinCertificate := ⟨⟨retention2131,(1955981423753964107/1000000000000000000),(1358828718451041/40000000000000000),(29354444920045191/3125000000000000),(161509788327666181233/125000000000000000),(1104503438159390663/500000000000000000)⟩,(24963343358780261/25000000000000000),(369050106420998699/1000000000000000000),(52613789566987427/200000000000000000),(88989445093740847/500000000000000000)⟩
theorem valid2131 : certificate2131.Valid := by decide +kernel
theorem sound2131 : certificate2131.Sound := rat_cut_bin_certificate_sound certificate2131 profilesValid2131 numericValid2131 valid2131

def retention2132 : RatCutRetentionCertificate := ⟨(27/1000),(7/250),(12253305534012554593/136867250224018312986),(1531391182366325001/1000000000000000000),(21/10),(2464161703367060472693/1280000000000000000000),true,MergedCutProfiles.Batch330.profile13201,![MergedCutProfiles.Batch330.profile13201,MergedCutProfiles.Batch039.profile1574,MergedCutProfiles.Batch330.profile13205,MergedCutProfiles.Batch330.profile13206,MergedCutProfiles.Batch330.profile13207,MergedCutProfiles.Batch330.profile13208,MergedCutProfiles.Batch330.profile13209,MergedCutProfiles.Batch330.profile13210,MergedCutProfiles.Batch330.profile13211,MergedCutProfiles.Batch330.profile13212,MergedCutProfiles.Batch330.profile13213,MergedCutProfiles.Batch330.profile13214,MergedCutProfiles.Batch330.profile13215,MergedCutProfiles.Batch330.profile13216,MergedCutProfiles.Batch330.profile13217,MergedCutProfiles.Batch330.profile13218]⟩
theorem profilesValid2132 : retention2132.ProfilesValid := by
  change ∀ j : Fin 16, (retention2132.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch330.valid13201
  · exact MergedCutProfiles.Batch039.valid1574
  · exact MergedCutProfiles.Batch330.valid13205
  · exact MergedCutProfiles.Batch330.valid13206
  · exact MergedCutProfiles.Batch330.valid13207
  · exact MergedCutProfiles.Batch330.valid13208
  · exact MergedCutProfiles.Batch330.valid13209
  · exact MergedCutProfiles.Batch330.valid13210
  · exact MergedCutProfiles.Batch330.valid13211
  · exact MergedCutProfiles.Batch330.valid13212
  · exact MergedCutProfiles.Batch330.valid13213
  · exact MergedCutProfiles.Batch330.valid13214
  · exact MergedCutProfiles.Batch330.valid13215
  · exact MergedCutProfiles.Batch330.valid13216
  · exact MergedCutProfiles.Batch330.valid13217
  · exact MergedCutProfiles.Batch330.valid13218
theorem numericValid2132 : retention2132.NumericValid := by decide +kernel
def certificate2132 : RatCutBinCertificate := ⟨⟨retention2132,(1955981423753964107/1000000000000000000),(1358828718451041/40000000000000000),(29354444920045191/3125000000000000),(161509788327666181233/125000000000000000),(955135737380426183/500000000000000000)⟩,(24963343358780261/25000000000000000),(380689857100555581/1000000000000000000),(251648807283449549/1000000000000000000),(285029650782021/1600000000000000)⟩
theorem valid2132 : certificate2132.Valid := by decide +kernel
theorem sound2132 : certificate2132.Sound := rat_cut_bin_certificate_sound certificate2132 profilesValid2132 numericValid2132 valid2132

def retention2133 : RatCutRetentionCertificate := ⟨(27/1000),(7/250),(20885136032888675205/45622416741339437662),(12253305534012554593/1000000000000000000),(21/20),(21209584679930011891518837029798416771791/19605288854420087348800000000000000000000),false,MergedCutProfiles.Batch330.profile13219,(fun _ => MergedCutProfiles.Batch330.profile13219)⟩
theorem profilesValid2133 : retention2133.ProfilesValid := by
  exact MergedCutProfiles.Batch330.valid13219
theorem numericValid2133 : retention2133.NumericValid := by decide +kernel
def certificate2133 : RatCutBinCertificate := ⟨⟨retention2133,(1955981423753964107/1000000000000000000),(1358828718451041/40000000000000000),(29354444920045191/3125000000000000),(161509788327666181233/125000000000000000),(33575073890000369/31250000000000000)⟩,(24963343358780261/25000000000000000),(112603171847520653/250000000000000000),(47585479152435849/250000000000000000),(90070954385869317/500000000000000000)⟩
theorem valid2133 : certificate2133.Valid := by decide +kernel
theorem sound2133 : certificate2133.Sound := rat_cut_bin_certificate_sound certificate2133 profilesValid2133 numericValid2133 valid2133

def retention2134 : RatCutRetentionCertificate := ⟨(27/1000),(7/250),(32000000000000000000/68433625112009156493),(12531081619733205123/200000000000000000),1,(2129351116274875120212124550459205583/2004973059157312819680000000000000000),false,MergedCutProfiles.Batch330.profile13220,(fun _ => MergedCutProfiles.Batch330.profile13220)⟩
theorem profilesValid2134 : retention2134.ProfilesValid := by
  exact MergedCutProfiles.Batch330.valid13220
theorem numericValid2134 : retention2134.NumericValid := by decide +kernel
def certificate2134 : RatCutBinCertificate := ⟨⟨retention2134,(1955981423753964107/1000000000000000000),(1358828718451041/40000000000000000),(29354444920045191/3125000000000000),(161509788327666181233/125000000000000000),(1054961091162517621/1000000000000000000)⟩,(24963343358780261/25000000000000000),(54026959902426473/125000000000000000),(205228106642766033/1000000000000000000),(106303852897475859/500000000000000000)⟩
theorem valid2134 : certificate2134.Valid := by decide +kernel
theorem sound2134 : certificate2134.Sound := rat_cut_bin_certificate_sound certificate2134 profilesValid2134 numericValid2134 valid2134

def retention2135 : RatCutRetentionCertificate := ⟨(27/1000),(7/250),(1/2),64,1,(63843694446586541505180302875124093631/64000000000000000000000000000000000000),false,MergedCutProfiles.Batch040.profile1621,(fun _ => MergedCutProfiles.Batch040.profile1621)⟩
theorem profilesValid2135 : retention2135.ProfilesValid := by
  exact MergedCutProfiles.Batch040.valid1621
theorem numericValid2135 : retention2135.NumericValid := by decide +kernel
def certificate2135 : RatCutBinCertificate := ⟨⟨retention2135,(1955981423753964107/1000000000000000000),(1358828718451041/40000000000000000),(29354444920045191/3125000000000000),(161509788327666181233/125000000000000000),(990484039702550327/1000000000000000000)⟩,(24963343358780261/25000000000000000),(46020726270307387/100000000000000000),(36527131760899761/200000000000000000),(177877348209352837/1000000000000000000)⟩
theorem valid2135 : certificate2135.Valid := by decide +kernel
theorem sound2135 : certificate2135.Sound := rat_cut_bin_certificate_sound certificate2135 profilesValid2135 numericValid2135 valid2135

def certificates : List RatCutBinCertificate := [certificate2124,certificate2125,certificate2126,certificate2127,certificate2128,certificate2129,certificate2130,certificate2131,certificate2132,certificate2133,certificate2134,certificate2135]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound2124,List.forall_mem_cons.mpr ⟨sound2125,List.forall_mem_cons.mpr ⟨sound2126,List.forall_mem_cons.mpr ⟨sound2127,List.forall_mem_cons.mpr ⟨sound2128,List.forall_mem_cons.mpr ⟨sound2129,List.forall_mem_cons.mpr ⟨sound2130,List.forall_mem_cons.mpr ⟨sound2131,List.forall_mem_cons.mpr ⟨sound2132,List.forall_mem_cons.mpr ⟨sound2133,List.forall_mem_cons.mpr ⟨sound2134,List.forall_mem_cons.mpr ⟨sound2135,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch177
