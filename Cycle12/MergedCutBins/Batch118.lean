import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch230
import Cycle12.MergedCutProfiles.Batch231
import Cycle12.MergedCutProfiles.Batch232

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch118

def retention1416 : RatCutRetentionCertificate := ⟨(243/4000),(61/1000),(1/2),(5984464345836657409/1000000000000000000),(11/10),(2381389746989698836154322863366102768439/2393785738334662963600000000000000000000),false,MergedCutProfiles.Batch230.profile9234,(fun _ => MergedCutProfiles.Batch230.profile9234)⟩
theorem profilesValid1416 : retention1416.ProfilesValid := by
  exact MergedCutProfiles.Batch230.valid9234
theorem numericValid1416 : retention1416.NumericValid := by decide +kernel
def certificate1416 : RatCutBinCertificate := ⟨⟨retention1416,(578929149816886571/250000000000000000),(9485872639178457/50000000000000000),(16081221812647658401/1000000000000000000),(193384223247665810983/1000000000000000000),(964765604160774459/1000000000000000000)⟩,(990252182657480397/1000000000000000000),(455771566834700739/1000000000000000000),(186099520354824931/1000000000000000000),(35627068872439557/250000000000000000)⟩
theorem valid1416 : certificate1416.Valid := by decide +kernel
theorem sound1416 : certificate1416.Sound := rat_cut_bin_certificate_sound certificate1416 profilesValid1416 numericValid1416 valid1416

def retention1417 : RatCutRetentionCertificate := ⟨(243/4000),(61/1000),(1/2),64,1,(63852346893339181453175647810443474591/64000000000000000000000000000000000000),false,MergedCutProfiles.Batch230.profile9234,(fun _ => MergedCutProfiles.Batch230.profile9234)⟩
theorem profilesValid1417 : retention1417.ProfilesValid := by
  exact MergedCutProfiles.Batch230.valid9234
theorem numericValid1417 : retention1417.NumericValid := by decide +kernel
def certificate1417 : RatCutBinCertificate := ⟨⟨retention1417,(578929149816886571/250000000000000000),(9485872639178457/50000000000000000),(16081221812647658401/1000000000000000000),(193384223247665810983/1000000000000000000),(60648309032419017/62500000000000000)⟩,(990252182657480397/1000000000000000000),(104234301085535449/250000000000000000),(218317133706502049/1000000000000000000),(206630992019246051/1000000000000000000)⟩
theorem valid1417 : certificate1417.Valid := by decide +kernel
theorem sound1417 : certificate1417.Sound := rat_cut_bin_certificate_sound certificate1417 profilesValid1417 numericValid1417 valid1417

def retention1418 : RatCutRetentionCertificate := ⟨(243/4000),(61/1000),(5626731393652078221/12006982453999286597),(359579035586901193/100000000000000000),(6/5),(474852347355551996335656431685976863/449473794483626491250000000000000000),false,MergedCutProfiles.Batch230.profile9235,(fun _ => MergedCutProfiles.Batch230.profile9235)⟩
theorem profilesValid1418 : retention1418.ProfilesValid := by
  exact MergedCutProfiles.Batch230.valid9235
theorem numericValid1418 : retention1418.NumericValid := by decide +kernel
def certificate1418 : RatCutBinCertificate := ⟨⟨retention1418,(664184885566886571/250000000000000000),(9485872639178457/50000000000000000),(16081221812647658401/1000000000000000000),(193384223247665810983/1000000000000000000),(1018842946733062623/1000000000000000000)⟩,(98881296166874239/100000000000000000),(389517891903321519/1000000000000000000),(121612541219379933/500000000000000000),(17041868467320197/100000000000000000)⟩
theorem valid1418 : certificate1418.Valid := by decide +kernel
theorem sound1418 : certificate1418.Sound := rat_cut_bin_certificate_sound certificate1418 profilesValid1418 numericValid1418 valid1418

def retention1419 : RatCutRetentionCertificate := ⟨(243/4000),(61/1000),(5913751243941513556/12006982453999286597),(5626731393652078221/1000000000000000000),(11/10),(2267448941925714008714674523705491216919/2250692557460831288400000000000000000000),false,MergedCutProfiles.Batch230.profile9236,(fun _ => MergedCutProfiles.Batch230.profile9236)⟩
theorem profilesValid1419 : retention1419.ProfilesValid := by
  exact MergedCutProfiles.Batch230.valid9236
theorem numericValid1419 : retention1419.NumericValid := by decide +kernel
def certificate1419 : RatCutBinCertificate := ⟨⟨retention1419,(664184885566886571/250000000000000000),(9485872639178457/50000000000000000),(16081221812647658401/1000000000000000000),(193384223247665810983/1000000000000000000),(972962490850124239/1000000000000000000)⟩,(98881296166874239/100000000000000000),(407885772086935303/1000000000000000000),(22633421618697727/100000000000000000),(173051604129964373/1000000000000000000)⟩
theorem valid1419 : certificate1419.Valid := by decide +kernel
theorem sound1419 : certificate1419.Sound := rat_cut_bin_certificate_sound certificate1419 profilesValid1419 numericValid1419 valid1419

def retention1420 : RatCutRetentionCertificate := ⟨(243/4000),(61/1000),(5972888756380928692/12006982453999286597),(1478437810985378389/250000000000000000),(21/20),(145677397775183067353820066026367836891/147843781098537838900000000000000000000),false,MergedCutProfiles.Batch230.profile9237,(fun _ => MergedCutProfiles.Batch230.profile9237)⟩
theorem profilesValid1420 : retention1420.ProfilesValid := by
  exact MergedCutProfiles.Batch230.valid9237
theorem numericValid1420 : retention1420.NumericValid := by decide +kernel
def certificate1420 : RatCutBinCertificate := ⟨⟨retention1420,(664184885566886571/250000000000000000),(9485872639178457/50000000000000000),(16081221812647658401/1000000000000000000),(193384223247665810983/1000000000000000000),(952431711543963313/1000000000000000000)⟩,(98881296166874239/100000000000000000),(5208477836021109/12500000000000000),(27317970784107609/125000000000000000),(170884692286661067/1000000000000000000)⟩
theorem valid1420 : certificate1420.Valid := by decide +kernel
theorem sound1420 : certificate1420.Sound := rat_cut_bin_certificate_sound certificate1420 profilesValid1420 numericValid1420 valid1420

def retention1421 : RatCutRetentionCertificate := ⟨(243/4000),(61/1000),(1/2),(1493222189095232173/250000000000000000),(21/20),(585897492484681569857003895854168237591/597288875638092869200000000000000000000),false,MergedCutProfiles.Batch230.profile9234,(fun _ => MergedCutProfiles.Batch230.profile9234)⟩
theorem profilesValid1421 : retention1421.ProfilesValid := by
  exact MergedCutProfiles.Batch230.valid9234
theorem numericValid1421 : retention1421.NumericValid := by decide +kernel
def certificate1421 : RatCutBinCertificate := ⟨⟨retention1421,(664184885566886571/250000000000000000),(9485872639178457/50000000000000000),(16081221812647658401/1000000000000000000),(193384223247665810983/1000000000000000000),(474006569875126757/500000000000000000)⟩,(98881296166874239/100000000000000000),(83724062494867867/200000000000000000),(216848151046993737/1000000000000000000),(169085789317952359/1000000000000000000)⟩
theorem valid1421 : certificate1421.Valid := by decide +kernel
theorem sound1421 : certificate1421.Sound := rat_cut_bin_certificate_sound certificate1421 profilesValid1421 numericValid1421 valid1421

def retention1422 : RatCutRetentionCertificate := ⟨(61/1000),(49/800),(893487663867829946/11890828153437861019),(425061427235076229/500000000000000000),(27/10),(78600444404105319111/40000000000000000000),true,MergedCutProfiles.Batch230.profile9238,![MergedCutProfiles.Batch230.profile9238,MergedCutProfiles.Batch230.profile9239,MergedCutProfiles.Batch231.profile9240,MergedCutProfiles.Batch231.profile9241,MergedCutProfiles.Batch231.profile9242,MergedCutProfiles.Batch231.profile9243,MergedCutProfiles.Batch231.profile9244,MergedCutProfiles.Batch231.profile9245,MergedCutProfiles.Batch231.profile9246,MergedCutProfiles.Batch231.profile9247,MergedCutProfiles.Batch231.profile9248,MergedCutProfiles.Batch231.profile9249,MergedCutProfiles.Batch231.profile9250,MergedCutProfiles.Batch231.profile9251,MergedCutProfiles.Batch231.profile9252,MergedCutProfiles.Batch231.profile9253]⟩
theorem profilesValid1422 : retention1422.ProfilesValid := by
  change ∀ j : Fin 16, (retention1422.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch230.valid9238
  · exact MergedCutProfiles.Batch230.valid9239
  · exact MergedCutProfiles.Batch231.valid9240
  · exact MergedCutProfiles.Batch231.valid9241
  · exact MergedCutProfiles.Batch231.valid9242
  · exact MergedCutProfiles.Batch231.valid9243
  · exact MergedCutProfiles.Batch231.valid9244
  · exact MergedCutProfiles.Batch231.valid9245
  · exact MergedCutProfiles.Batch231.valid9246
  · exact MergedCutProfiles.Batch231.valid9247
  · exact MergedCutProfiles.Batch231.valid9248
  · exact MergedCutProfiles.Batch231.valid9249
  · exact MergedCutProfiles.Batch231.valid9250
  · exact MergedCutProfiles.Batch231.valid9251
  · exact MergedCutProfiles.Batch231.valid9252
  · exact MergedCutProfiles.Batch231.valid9253
theorem numericValid1422 : retention1422.NumericValid := by decide +kernel
def certificate1422 : RatCutBinCertificate := ⟨⟨retention1422,(292104511969665911/125000000000000000),(191571141137618907/1000000000000000000),(16155495474611876117/1000000000000000000),(192398482326285571833/1000000000000000000),(378032278230728429/200000000000000000)⟩,(495067365838166397/500000000000000000),(87169015035586939/250000000000000000),(283948630968471589/1000000000000000000),(150506949652923923/1000000000000000000)⟩
theorem valid1422 : certificate1422.Valid := by decide +kernel
theorem sound1422 : certificate1422.Sound := rat_cut_bin_certificate_sound certificate1422 profilesValid1422 numericValid1422 valid1422

def retention1423 : RatCutRetentionCertificate := ⟨(61/1000),(49/800),(1145837167297308611/11890828153437861019),(446743831933914973/500000000000000000),(13/5),(305630601984261859197/160000000000000000000),true,MergedCutProfiles.Batch231.profile9254,![MergedCutProfiles.Batch231.profile9254,MergedCutProfiles.Batch231.profile9255,MergedCutProfiles.Batch231.profile9256,MergedCutProfiles.Batch231.profile9257,MergedCutProfiles.Batch231.profile9258,MergedCutProfiles.Batch231.profile9259,MergedCutProfiles.Batch231.profile9260,MergedCutProfiles.Batch231.profile9261,MergedCutProfiles.Batch231.profile9262,MergedCutProfiles.Batch231.profile9263,MergedCutProfiles.Batch231.profile9264,MergedCutProfiles.Batch231.profile9265,MergedCutProfiles.Batch231.profile9266,MergedCutProfiles.Batch231.profile9267,MergedCutProfiles.Batch231.profile9268,MergedCutProfiles.Batch231.profile9269]⟩
theorem profilesValid1423 : retention1423.ProfilesValid := by
  change ∀ j : Fin 16, (retention1423.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch231.valid9254
  · exact MergedCutProfiles.Batch231.valid9255
  · exact MergedCutProfiles.Batch231.valid9256
  · exact MergedCutProfiles.Batch231.valid9257
  · exact MergedCutProfiles.Batch231.valid9258
  · exact MergedCutProfiles.Batch231.valid9259
  · exact MergedCutProfiles.Batch231.valid9260
  · exact MergedCutProfiles.Batch231.valid9261
  · exact MergedCutProfiles.Batch231.valid9262
  · exact MergedCutProfiles.Batch231.valid9263
  · exact MergedCutProfiles.Batch231.valid9264
  · exact MergedCutProfiles.Batch231.valid9265
  · exact MergedCutProfiles.Batch231.valid9266
  · exact MergedCutProfiles.Batch231.valid9267
  · exact MergedCutProfiles.Batch231.valid9268
  · exact MergedCutProfiles.Batch231.valid9269
theorem numericValid1423 : retention1423.NumericValid := by decide +kernel
def certificate1423 : RatCutBinCertificate := ⟨⟨retention1423,(292104511969665911/125000000000000000),(191571141137618907/1000000000000000000),(16155495474611876117/1000000000000000000),(192398482326285571833/1000000000000000000),(1838114128412388713/1000000000000000000)⟩,(495067365838166397/500000000000000000),(43922400251800533/125000000000000000),(70277866121875379/250000000000000000),(150553923349163911/1000000000000000000)⟩
theorem valid1423 : certificate1423.Valid := by decide +kernel
theorem sound1423 : certificate1423.Sound := rat_cut_bin_certificate_sound certificate1423 profilesValid1423 numericValid1423 valid1423

def retention1424 : RatCutRetentionCertificate := ⟨(61/1000),(49/800),(2254116315535900294/11890828153437861019),(1145837167297308611/1000000000000000000),(21/10),(2122252079455945642023/1280000000000000000000),true,MergedCutProfiles.Batch231.profile9270,![MergedCutProfiles.Batch231.profile9270,MergedCutProfiles.Batch231.profile9271,MergedCutProfiles.Batch231.profile9272,MergedCutProfiles.Batch231.profile9273,MergedCutProfiles.Batch231.profile9274,MergedCutProfiles.Batch231.profile9275,MergedCutProfiles.Batch231.profile9276,MergedCutProfiles.Batch231.profile9277,MergedCutProfiles.Batch231.profile9278,MergedCutProfiles.Batch231.profile9279,MergedCutProfiles.Batch232.profile9280,MergedCutProfiles.Batch232.profile9281,MergedCutProfiles.Batch232.profile9282,MergedCutProfiles.Batch232.profile9283,MergedCutProfiles.Batch232.profile9284,MergedCutProfiles.Batch232.profile9285]⟩
theorem profilesValid1424 : retention1424.ProfilesValid := by
  change ∀ j : Fin 16, (retention1424.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch231.valid9270
  · exact MergedCutProfiles.Batch231.valid9271
  · exact MergedCutProfiles.Batch231.valid9272
  · exact MergedCutProfiles.Batch231.valid9273
  · exact MergedCutProfiles.Batch231.valid9274
  · exact MergedCutProfiles.Batch231.valid9275
  · exact MergedCutProfiles.Batch231.valid9276
  · exact MergedCutProfiles.Batch231.valid9277
  · exact MergedCutProfiles.Batch231.valid9278
  · exact MergedCutProfiles.Batch231.valid9279
  · exact MergedCutProfiles.Batch232.valid9280
  · exact MergedCutProfiles.Batch232.valid9281
  · exact MergedCutProfiles.Batch232.valid9282
  · exact MergedCutProfiles.Batch232.valid9283
  · exact MergedCutProfiles.Batch232.valid9284
  · exact MergedCutProfiles.Batch232.valid9285
theorem numericValid1424 : retention1424.NumericValid := by decide +kernel
def certificate1424 : RatCutBinCertificate := ⟨⟨retention1424,(292104511969665911/125000000000000000),(191571141137618907/1000000000000000000),(16155495474611876117/1000000000000000000),(192398482326285571833/1000000000000000000),(1599794152681563681/1000000000000000000)⟩,(495067365838166397/500000000000000000),(184078705520729467/500000000000000000),(6598994980366067/25000000000000000),(150927987635135647/1000000000000000000)⟩
theorem valid1424 : certificate1424.Valid := by decide +kernel
theorem sound1424 : certificate1424.Sound := rat_cut_bin_certificate_sound certificate1424 profilesValid1424 numericValid1424 valid1424

def retention1425 : RatCutRetentionCertificate := ⟨(61/1000),(49/800),(4523478050119814925/11890828153437861019),(1127058157767950147/500000000000000000),(13/10),(779875259534151395863/640000000000000000000),true,MergedCutProfiles.Batch231.profile9271,![MergedCutProfiles.Batch231.profile9271,MergedCutProfiles.Batch232.profile9286,MergedCutProfiles.Batch231.profile9275,MergedCutProfiles.Batch232.profile9287,MergedCutProfiles.Batch232.profile9288,MergedCutProfiles.Batch232.profile9289,MergedCutProfiles.Batch232.profile9290,MergedCutProfiles.Batch232.profile9291,MergedCutProfiles.Batch232.profile9292,MergedCutProfiles.Batch232.profile9293,MergedCutProfiles.Batch232.profile9294,MergedCutProfiles.Batch232.profile9295,MergedCutProfiles.Batch232.profile9296,MergedCutProfiles.Batch232.profile9297,MergedCutProfiles.Batch232.profile9298,MergedCutProfiles.Batch232.profile9299]⟩
theorem profilesValid1425 : retention1425.ProfilesValid := by
  change ∀ j : Fin 16, (retention1425.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch231.valid9271
  · exact MergedCutProfiles.Batch232.valid9286
  · exact MergedCutProfiles.Batch231.valid9275
  · exact MergedCutProfiles.Batch232.valid9287
  · exact MergedCutProfiles.Batch232.valid9288
  · exact MergedCutProfiles.Batch232.valid9289
  · exact MergedCutProfiles.Batch232.valid9290
  · exact MergedCutProfiles.Batch232.valid9291
  · exact MergedCutProfiles.Batch232.valid9292
  · exact MergedCutProfiles.Batch232.valid9293
  · exact MergedCutProfiles.Batch232.valid9294
  · exact MergedCutProfiles.Batch232.valid9295
  · exact MergedCutProfiles.Batch232.valid9296
  · exact MergedCutProfiles.Batch232.valid9297
  · exact MergedCutProfiles.Batch232.valid9298
  · exact MergedCutProfiles.Batch232.valid9299
theorem numericValid1425 : retention1425.NumericValid := by decide +kernel
def certificate1425 : RatCutBinCertificate := ⟨⟨retention1425,(292104511969665911/125000000000000000),(191571141137618907/1000000000000000000),(16155495474611876117/1000000000000000000),(192398482326285571833/1000000000000000000),(591259862901817863/500000000000000000)⟩,(495067365838166397/500000000000000000),(207152567305231219/500000000000000000),(220627977585720499/1000000000000000000),(151392620231619701/1000000000000000000)⟩
theorem valid1425 : certificate1425.Valid := by decide +kernel
theorem sound1425 : certificate1425.Sound := rat_cut_bin_certificate_sound certificate1425 profilesValid1425 numericValid1425 valid1425

def retention1426 : RatCutRetentionCertificate := ⟨(61/1000),(49/800),(5630444870219304969/11890828153437861019),(180939122004792597/40000000000000000),1,(51491899208046915753/51200000000000000000),true,MergedCutProfiles.Batch232.profile9300,![MergedCutProfiles.Batch232.profile9300,MergedCutProfiles.Batch231.profile9274,MergedCutProfiles.Batch232.profile9301,MergedCutProfiles.Batch231.profile9279,MergedCutProfiles.Batch232.profile9302,MergedCutProfiles.Batch232.profile9284,MergedCutProfiles.Batch232.profile9303,MergedCutProfiles.Batch232.profile9304,MergedCutProfiles.Batch232.profile9305,MergedCutProfiles.Batch232.profile9306,MergedCutProfiles.Batch232.profile9307,MergedCutProfiles.Batch232.profile9308,MergedCutProfiles.Batch232.profile9309,MergedCutProfiles.Batch232.profile9310,MergedCutProfiles.Batch232.profile9311,MergedCutProfiles.Batch232.profile9312]⟩
theorem profilesValid1426 : retention1426.ProfilesValid := by
  change ∀ j : Fin 16, (retention1426.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch232.valid9300
  · exact MergedCutProfiles.Batch231.valid9274
  · exact MergedCutProfiles.Batch232.valid9301
  · exact MergedCutProfiles.Batch231.valid9279
  · exact MergedCutProfiles.Batch232.valid9302
  · exact MergedCutProfiles.Batch232.valid9284
  · exact MergedCutProfiles.Batch232.valid9303
  · exact MergedCutProfiles.Batch232.valid9304
  · exact MergedCutProfiles.Batch232.valid9305
  · exact MergedCutProfiles.Batch232.valid9306
  · exact MergedCutProfiles.Batch232.valid9307
  · exact MergedCutProfiles.Batch232.valid9308
  · exact MergedCutProfiles.Batch232.valid9309
  · exact MergedCutProfiles.Batch232.valid9310
  · exact MergedCutProfiles.Batch232.valid9311
  · exact MergedCutProfiles.Batch232.valid9312
theorem numericValid1426 : retention1426.NumericValid := by decide +kernel
def certificate1426 : RatCutBinCertificate := ⟨⟨retention1426,(292104511969665911/125000000000000000),(191571141137618907/1000000000000000000),(16155495474611876117/1000000000000000000),(192398482326285571833/1000000000000000000),(122248119904980929/125000000000000000)⟩,(495067365838166397/500000000000000000),(112104743825385461/250000000000000000),(959682420003221/5000000000000000),(30529210803872403/200000000000000000)⟩
theorem valid1426 : certificate1426.Valid := by decide +kernel
theorem sound1426 : certificate1426.Sound := rat_cut_bin_certificate_sound certificate1426 profilesValid1426 numericValid1426 valid1426

def retention1427 : RatCutRetentionCertificate := ⟨(61/1000),(49/800),(5859063510034138332/11890828153437861019),(5630444870219304969/1000000000000000000),(11/10),(2268076103985159533226280661460184659839/2252177948087721987600000000000000000000),false,MergedCutProfiles.Batch232.profile9313,(fun _ => MergedCutProfiles.Batch232.profile9313)⟩
theorem profilesValid1427 : retention1427.ProfilesValid := by
  exact MergedCutProfiles.Batch232.valid9313
theorem numericValid1427 : retention1427.NumericValid := by decide +kernel
def certificate1427 : RatCutBinCertificate := ⟨⟨retention1427,(292104511969665911/125000000000000000),(191571141137618907/1000000000000000000),(16155495474611876117/1000000000000000000),(192398482326285571833/1000000000000000000),(488286503176302447/500000000000000000)⟩,(495067365838166397/500000000000000000),(438793575477070193/1000000000000000000),(9988013128118309/50000000000000000),(30689232493683497/200000000000000000)⟩
theorem valid1427 : certificate1427.Valid := by decide +kernel
theorem sound1427 : certificate1427.Sound := rat_cut_bin_certificate_sound certificate1427 profilesValid1427 numericValid1427 valid1427

def certificates : List RatCutBinCertificate := [certificate1416,certificate1417,certificate1418,certificate1419,certificate1420,certificate1421,certificate1422,certificate1423,certificate1424,certificate1425,certificate1426,certificate1427]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound1416,List.forall_mem_cons.mpr ⟨sound1417,List.forall_mem_cons.mpr ⟨sound1418,List.forall_mem_cons.mpr ⟨sound1419,List.forall_mem_cons.mpr ⟨sound1420,List.forall_mem_cons.mpr ⟨sound1421,List.forall_mem_cons.mpr ⟨sound1422,List.forall_mem_cons.mpr ⟨sound1423,List.forall_mem_cons.mpr ⟨sound1424,List.forall_mem_cons.mpr ⟨sound1425,List.forall_mem_cons.mpr ⟨sound1426,List.forall_mem_cons.mpr ⟨sound1427,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch118
