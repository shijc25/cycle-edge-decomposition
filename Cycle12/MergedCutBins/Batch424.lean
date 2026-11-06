import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch707
import Cycle12.MergedCutProfiles.Batch708
import Cycle12.MergedCutProfiles.Batch709

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch424

def retention5088 : RatCutRetentionCertificate := ⟨(29/500),(59/1000),(86896961990763541/40602522845498831137),(876748866049168013/1000000000000000000),(18/5),(4822266758192581918176443352469100211/1992611059202654575000000000000000000),false,MergedCutProfiles.Batch707.profile28301,(fun _ => MergedCutProfiles.Batch707.profile28301)⟩
theorem profilesValid5088 : retention5088.ProfilesValid := by
  exact MergedCutProfiles.Batch707.valid28301
theorem numericValid5088 : retention5088.NumericValid := by decide +kernel
def certificate5088 : RatCutBinCertificate := ⟨⟨retention5088,(9847147918038829/5000000000000000),(175338961017292427/1000000000000000000),(478212759694574073/31250000000000000),(2500426975050413791941/125000000000000000),(467767544984313173/200000000000000000)⟩,(999918127938741009/1000000000000000000),(24065839560762093/31250000000000000),(7180302009887129/250000000000000000),(7736419961728257/500000000000000000)⟩
theorem valid5088 : certificate5088.Valid := by decide +kernel
theorem sound5088 : certificate5088.Sound := rat_cut_bin_certificate_sound certificate5088 profilesValid5088 numericValid5088 valid5088

def retention5089 : RatCutRetentionCertificate := ⟨(29/500),(59/1000),(29398160602558104477/1299280731055962596384),(86896961990763541/31250000000000000),(7/4),(24929771287648289230923778073833478919/11122811134817733248000000000000000000),false,MergedCutProfiles.Batch707.profile28302,(fun _ => MergedCutProfiles.Batch707.profile28302)⟩
theorem profilesValid5089 : retention5089.ProfilesValid := by
  exact MergedCutProfiles.Batch707.valid28302
theorem numericValid5089 : retention5089.NumericValid := by decide +kernel
def certificate5089 : RatCutBinCertificate := ⟨⟨retention5089,(9847147918038829/5000000000000000),(175338961017292427/1000000000000000000),(478212759694574073/31250000000000000),(2500426975050413791941/125000000000000000),(2201829352324359983/1000000000000000000)⟩,(999918127938741009/1000000000000000000),(35651331433243803/50000000000000000),(9160346310832639/200000000000000000),(17884450706881/390625000000000)⟩
theorem valid5089 : certificate5089.Valid := by decide +kernel
theorem sound5089 : certificate5089.Sound := rat_cut_bin_certificate_sound certificate5089 profilesValid5089 numericValid5089 valid5089

def retention5090 : RatCutRetentionCertificate := ⟨(29/500),(59/1000),(1/40),(29398160602558104477/1000000000000000000),(21/20),(34881832674028926482116609606157192231637/15679018988030989054400000000000000000000),false,MergedCutProfiles.Batch707.profile28303,(fun _ => MergedCutProfiles.Batch707.profile28303)⟩
theorem profilesValid5090 : retention5090.ProfilesValid := by
  exact MergedCutProfiles.Batch707.valid28303
theorem numericValid5090 : retention5090.NumericValid := by decide +kernel
def certificate5090 : RatCutBinCertificate := ⟨⟨retention5090,(9847147918038829/5000000000000000),(175338961017292427/1000000000000000000),(478212759694574073/31250000000000000),(2500426975050413791941/125000000000000000),(275131491506962927/125000000000000000)⟩,(999918127938741009/1000000000000000000),(669485163050198491/1000000000000000000),(15471602212081023/250000000000000000),(6073449589473159/50000000000000000)⟩
theorem valid5090 : certificate5090.Valid := by decide +kernel
theorem sound5090 : certificate5090.Sound := rat_cut_bin_certificate_sound certificate5090 profilesValid5090 numericValid5090 valid5090

def retention5091 : RatCutRetentionCertificate := ⟨(59/1000),(3/50),(214552819315865186/416232034516382991125),(77317890830969837/125000000000000000),4,(4642802382427349239/2000000000000000000),true,MergedCutProfiles.Batch707.profile28304,![MergedCutProfiles.Batch707.profile28304,MergedCutProfiles.Batch707.profile28305,MergedCutProfiles.Batch707.profile28306,MergedCutProfiles.Batch707.profile28307,MergedCutProfiles.Batch707.profile28308,MergedCutProfiles.Batch707.profile28309,MergedCutProfiles.Batch707.profile28310,MergedCutProfiles.Batch707.profile28311,MergedCutProfiles.Batch707.profile28312,MergedCutProfiles.Batch707.profile28313,MergedCutProfiles.Batch707.profile28314,MergedCutProfiles.Batch707.profile28315,MergedCutProfiles.Batch707.profile28316,MergedCutProfiles.Batch707.profile28317,MergedCutProfiles.Batch707.profile28318,MergedCutProfiles.Batch707.profile28319]⟩
theorem profilesValid5091 : retention5091.ProfilesValid := by
  change ∀ j : Fin 16, (retention5091.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch707.valid28304
  · exact MergedCutProfiles.Batch707.valid28305
  · exact MergedCutProfiles.Batch707.valid28306
  · exact MergedCutProfiles.Batch707.valid28307
  · exact MergedCutProfiles.Batch707.valid28308
  · exact MergedCutProfiles.Batch707.valid28309
  · exact MergedCutProfiles.Batch707.valid28310
  · exact MergedCutProfiles.Batch707.valid28311
  · exact MergedCutProfiles.Batch707.valid28312
  · exact MergedCutProfiles.Batch707.valid28313
  · exact MergedCutProfiles.Batch707.valid28314
  · exact MergedCutProfiles.Batch707.valid28315
  · exact MergedCutProfiles.Batch707.valid28316
  · exact MergedCutProfiles.Batch707.valid28317
  · exact MergedCutProfiles.Batch707.valid28318
  · exact MergedCutProfiles.Batch707.valid28319
theorem numericValid5091 : retention5091.NumericValid := by decide +kernel
def certificate5091 : RatCutBinCertificate := ⟨⟨retention5091,(1956748316365112229/1000000000000000000),(182428996879551849/1000000000000000000),(15581512187564472011/1000000000000000000),(19575556805189512953233/1000000000000000000),(278720260160543141/125000000000000000)⟩,(499958783231249059/500000000000000000),(138762614818438253/200000000000000000),(52561683060899117/1000000000000000000),(47819997575309/2000000000000000)⟩
theorem valid5091 : certificate5091.Valid := by decide +kernel
theorem sound5091 : certificate5091.Sound := rat_cut_bin_certificate_sound certificate5091 profilesValid5091 numericValid5091 valid5091

def retention5092 : RatCutRetentionCertificate := ⟨(59/1000),(3/50),(8515999144000000/9989568828393191787),(321829228973797779/500000000000000000),4,(1212917645457149297078125755526055011/514926766358076446400000000000000000),true,MergedCutProfiles.Batch708.profile28320,![MergedCutProfiles.Batch708.profile28320,MergedCutProfiles.Batch708.profile28321,MergedCutProfiles.Batch707.profile28308,MergedCutProfiles.Batch708.profile28322,MergedCutProfiles.Batch708.profile28323,MergedCutProfiles.Batch707.profile28313,MergedCutProfiles.Batch708.profile28324,MergedCutProfiles.Batch708.profile28325,MergedCutProfiles.Batch708.profile28326,MergedCutProfiles.Batch708.profile28327,MergedCutProfiles.Batch708.profile28328,MergedCutProfiles.Batch708.profile28329,MergedCutProfiles.Batch708.profile28330,MergedCutProfiles.Batch708.profile28331,MergedCutProfiles.Batch708.profile28332,MergedCutProfiles.Batch708.profile28333]⟩
theorem profilesValid5092 : retention5092.ProfilesValid := by
  change ∀ j : Fin 16, (retention5092.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch708.valid28320
  · exact MergedCutProfiles.Batch708.valid28321
  · exact MergedCutProfiles.Batch707.valid28308
  · exact MergedCutProfiles.Batch708.valid28322
  · exact MergedCutProfiles.Batch708.valid28323
  · exact MergedCutProfiles.Batch707.valid28313
  · exact MergedCutProfiles.Batch708.valid28324
  · exact MergedCutProfiles.Batch708.valid28325
  · exact MergedCutProfiles.Batch708.valid28326
  · exact MergedCutProfiles.Batch708.valid28327
  · exact MergedCutProfiles.Batch708.valid28328
  · exact MergedCutProfiles.Batch708.valid28329
  · exact MergedCutProfiles.Batch708.valid28330
  · exact MergedCutProfiles.Batch708.valid28331
  · exact MergedCutProfiles.Batch708.valid28332
  · exact MergedCutProfiles.Batch708.valid28333
theorem numericValid5092 : retention5092.NumericValid := by decide +kernel
def certificate5092 : RatCutBinCertificate := ⟨⟨retention5092,(1956748316365112229/1000000000000000000),(182428996879551849/1000000000000000000),(15581512187564472011/1000000000000000000),(19575556805189512953233/1000000000000000000),(226387575477839753/100000000000000000)⟩,(499958783231249059/500000000000000000),(166520540859061749/250000000000000000),(31630256596457849/500000000000000000),(1467417247220081/50000000000000000)⟩
theorem valid5092 : certificate5092.Valid := by decide +kernel
theorem sound5092 : certificate5092.Sound := rat_cut_bin_certificate_sound certificate5092 profilesValid5092 numericValid5092 valid5092

def retention5093 : RatCutRetentionCertificate := ⟨(59/1000),(3/50),(2001207360961554401/1248696103549148973375),(1064499893/1000000000),(59/20),(16428936223073476562333865906924711/6812799315200000000000000000000000),true,MergedCutProfiles.Batch707.profile28306,![MergedCutProfiles.Batch707.profile28306,MergedCutProfiles.Batch707.profile28309,MergedCutProfiles.Batch708.profile28334,MergedCutProfiles.Batch707.profile28315,MergedCutProfiles.Batch707.profile28318,MergedCutProfiles.Batch708.profile28335,MergedCutProfiles.Batch708.profile28336,MergedCutProfiles.Batch708.profile28332,MergedCutProfiles.Batch708.profile28337,MergedCutProfiles.Batch708.profile28338,MergedCutProfiles.Batch708.profile28339,MergedCutProfiles.Batch708.profile28340,MergedCutProfiles.Batch708.profile28341,MergedCutProfiles.Batch708.profile28342,MergedCutProfiles.Batch708.profile28343,MergedCutProfiles.Batch708.profile28344]⟩
theorem profilesValid5093 : retention5093.ProfilesValid := by
  change ∀ j : Fin 16, (retention5093.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch707.valid28306
  · exact MergedCutProfiles.Batch707.valid28309
  · exact MergedCutProfiles.Batch708.valid28334
  · exact MergedCutProfiles.Batch707.valid28315
  · exact MergedCutProfiles.Batch707.valid28318
  · exact MergedCutProfiles.Batch708.valid28335
  · exact MergedCutProfiles.Batch708.valid28336
  · exact MergedCutProfiles.Batch708.valid28332
  · exact MergedCutProfiles.Batch708.valid28337
  · exact MergedCutProfiles.Batch708.valid28338
  · exact MergedCutProfiles.Batch708.valid28339
  · exact MergedCutProfiles.Batch708.valid28340
  · exact MergedCutProfiles.Batch708.valid28341
  · exact MergedCutProfiles.Batch708.valid28342
  · exact MergedCutProfiles.Batch708.valid28343
  · exact MergedCutProfiles.Batch708.valid28344
theorem numericValid5093 : retention5093.NumericValid := by decide +kernel
def certificate5093 : RatCutBinCertificate := ⟨⟨retention5093,(1956748316365112229/1000000000000000000),(182428996879551849/1000000000000000000),(15581512187564472011/1000000000000000000),(19575556805189512953233/1000000000000000000),(93755889107729851/40000000000000000)⟩,(499958783231249059/500000000000000000),(120218984981050009/250000000000000000),(16705258277888049/100000000000000000),(52959085319385543/500000000000000000)⟩
theorem valid5093 : certificate5093.Valid := by decide +kernel
theorem sound5093 : certificate5093.Sound := rat_cut_bin_certificate_sound certificate5093 profilesValid5093 numericValid5093 valid5093

def retention5094 : RatCutRetentionCertificate := ⟨(59/1000),(3/50),(512000000000000000/9989568828393191787),(2001207360961554401/1000000000000000000),(19/10),(2679544865059335682477/1280000000000000000000),true,MergedCutProfiles.Batch708.profile28345,![MergedCutProfiles.Batch708.profile28345,MergedCutProfiles.Batch708.profile28346,MergedCutProfiles.Batch708.profile28347,MergedCutProfiles.Batch708.profile28348,MergedCutProfiles.Batch708.profile28349,MergedCutProfiles.Batch708.profile28350,MergedCutProfiles.Batch708.profile28351,MergedCutProfiles.Batch708.profile28352,MergedCutProfiles.Batch708.profile28353,MergedCutProfiles.Batch708.profile28354,MergedCutProfiles.Batch708.profile28355,MergedCutProfiles.Batch708.profile28356,MergedCutProfiles.Batch708.profile28357,MergedCutProfiles.Batch708.profile28358,MergedCutProfiles.Batch708.profile28359,MergedCutProfiles.Batch709.profile28360]⟩
theorem profilesValid5094 : retention5094.ProfilesValid := by
  change ∀ j : Fin 16, (retention5094.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch708.valid28345
  · exact MergedCutProfiles.Batch708.valid28346
  · exact MergedCutProfiles.Batch708.valid28347
  · exact MergedCutProfiles.Batch708.valid28348
  · exact MergedCutProfiles.Batch708.valid28349
  · exact MergedCutProfiles.Batch708.valid28350
  · exact MergedCutProfiles.Batch708.valid28351
  · exact MergedCutProfiles.Batch708.valid28352
  · exact MergedCutProfiles.Batch708.valid28353
  · exact MergedCutProfiles.Batch708.valid28354
  · exact MergedCutProfiles.Batch708.valid28355
  · exact MergedCutProfiles.Batch708.valid28356
  · exact MergedCutProfiles.Batch708.valid28357
  · exact MergedCutProfiles.Batch708.valid28358
  · exact MergedCutProfiles.Batch708.valid28359
  · exact MergedCutProfiles.Batch709.valid28360
theorem numericValid5094 : retention5094.NumericValid := by decide +kernel
def certificate5094 : RatCutBinCertificate := ⟨⟨retention5094,(1956748316365112229/1000000000000000000),(182428996879551849/1000000000000000000),(15581512187564472011/1000000000000000000),(19575556805189512953233/1000000000000000000),(2049865905879530159/1000000000000000000)⟩,(499958783231249059/500000000000000000),(20843040438335839/50000000000000000),(218383971158174247/1000000000000000000),(45878914337207613/250000000000000000)⟩
theorem valid5094 : certificate5094.Valid := by decide +kernel
theorem sound5094 : certificate5094.Sound := rat_cut_bin_certificate_sound certificate5094 profilesValid5094 numericValid5094 valid5094

def retention5095 : RatCutRetentionCertificate := ⟨(59/1000),(3/50),(1/2),64,1,(255406652144878890858729144973698939999/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch709.profile28361,(fun _ => MergedCutProfiles.Batch709.profile28361)⟩
theorem profilesValid5095 : retention5095.ProfilesValid := by
  exact MergedCutProfiles.Batch709.valid28361
theorem numericValid5095 : retention5095.NumericValid := by decide +kernel
def certificate5095 : RatCutBinCertificate := ⟨⟨retention5095,(1956748316365112229/1000000000000000000),(182428996879551849/1000000000000000000),(15581512187564472011/1000000000000000000),(19575556805189512953233/1000000000000000000),(121846567551793851/125000000000000000)⟩,(499958783231249059/500000000000000000),(568736718348537507/1000000000000000000),(55151864203968279/500000000000000000),(52949575625794121/500000000000000000)⟩
theorem valid5095 : certificate5095.Valid := by decide +kernel
theorem sound5095 : certificate5095.Sound := rat_cut_bin_certificate_sound certificate5095 profilesValid5095 numericValid5095 valid5095

def retention5096 : RatCutRetentionCertificate := ⟨(59/1000),(3/50),(512000000000000000/9989568828393191787),(22691123924733440863/500000000000000000),1,(377663679419006493386695535370287138079/181528991397867526904000000000000000000),false,MergedCutProfiles.Batch709.profile28362,(fun _ => MergedCutProfiles.Batch709.profile28362)⟩
theorem profilesValid5096 : retention5096.ProfilesValid := by
  exact MergedCutProfiles.Batch709.valid28362
theorem numericValid5096 : retention5096.NumericValid := by decide +kernel
def certificate5096 : RatCutBinCertificate := ⟨⟨retention5096,(1725128581365112229/1000000000000000000),(182428996879551849/1000000000000000000),(15581512187564472011/1000000000000000000),(19575556805189512953233/1000000000000000000),(515065355993595901/250000000000000000)⟩,(199985464849476629/200000000000000000),(7952852714011717/500000000000000000),(443275300949103967/500000000000000000),(109192324813627423/62500000000000000)⟩
theorem valid5096 : certificate5096.Valid := by decide +kernel
theorem sound5096 : certificate5096.Sound := rat_cut_bin_certificate_sound certificate5096 profilesValid5096 numericValid5096 valid5096

def retention5097 : RatCutRetentionCertificate := ⟨(59/1000),(3/50),(1/2),64,1,(255406652144878890858729144973698939999/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch709.profile28361,(fun _ => MergedCutProfiles.Batch709.profile28361)⟩
theorem profilesValid5097 : retention5097.ProfilesValid := by
  exact MergedCutProfiles.Batch709.valid28361
theorem numericValid5097 : retention5097.NumericValid := by decide +kernel
def certificate5097 : RatCutBinCertificate := ⟨⟨retention5097,(1725128581365112229/1000000000000000000),(182428996879551849/1000000000000000000),(15581512187564472011/1000000000000000000),(19575556805189512953233/1000000000000000000),(61092772147587309/62500000000000000)⟩,(199985464849476629/200000000000000000),(33524742537557693/1000000000000000000),(834072303714878069/1000000000000000000),(802968721111830619/1000000000000000000)⟩
theorem valid5097 : certificate5097.Valid := by decide +kernel
theorem sound5097 : certificate5097.Sound := rat_cut_bin_certificate_sound certificate5097 profilesValid5097 numericValid5097 valid5097

def retention5098 : RatCutRetentionCertificate := ⟨(59/1000),(3/50),(759369877973857813/1248696103549148973375),(75185136433055229/100000000000000000),4,(1842427987940294995986271759529188751/751851364330552290000000000000000000),false,MergedCutProfiles.Batch709.profile28363,(fun _ => MergedCutProfiles.Batch709.profile28363)⟩
theorem profilesValid5098 : retention5098.ProfilesValid := by
  exact MergedCutProfiles.Batch709.valid28363
theorem numericValid5098 : retention5098.NumericValid := by decide +kernel
def certificate5098 : RatCutBinCertificate := ⟨⟨retention5098,(1978102063365112229/1000000000000000000),(182428996879551849/1000000000000000000),(15581512187564472011/1000000000000000000),(19575556805189512953233/1000000000000000000),(2357882478862660333/1000000000000000000)⟩,(999916666859785693/1000000000000000000),(12242880371756891/15625000000000000),(5065509580810493/200000000000000000),(2496366390391769/200000000000000000)⟩
theorem valid5098 : certificate5098.Valid := by decide +kernel
theorem sound5098 : certificate5098.Sound := rat_cut_bin_certificate_sound certificate5098 profilesValid5098 numericValid5098 valid5098

def retention5099 : RatCutRetentionCertificate := ⟨(59/1000),(3/50),(872876093040349478/1248696103549148973375),(759369877973857813/1000000000000000000),4,(465298166865931046614879044271606869/189842469493464453250000000000000000),false,MergedCutProfiles.Batch709.profile28364,(fun _ => MergedCutProfiles.Batch709.profile28364)⟩
theorem profilesValid5099 : retention5099.ProfilesValid := by
  exact MergedCutProfiles.Batch709.valid28364
theorem numericValid5099 : retention5099.NumericValid := by decide +kernel
def certificate5099 : RatCutBinCertificate := ⟨⟨retention5099,(1978102063365112229/1000000000000000000),(182428996879551849/1000000000000000000),(15581512187564472011/1000000000000000000),(19575556805189512953233/1000000000000000000),(147395671727136441/62500000000000000)⟩,(999916666859785693/1000000000000000000),(781763633225585647/1000000000000000000),(25763937385100603/1000000000000000000),(12719554060104801/1000000000000000000)⟩
theorem valid5099 : certificate5099.Valid := by decide +kernel
theorem sound5099 : certificate5099.Sound := rat_cut_bin_certificate_sound certificate5099 profilesValid5099 numericValid5099 valid5099

def certificates : List RatCutBinCertificate := [certificate5088,certificate5089,certificate5090,certificate5091,certificate5092,certificate5093,certificate5094,certificate5095,certificate5096,certificate5097,certificate5098,certificate5099]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound5088,List.forall_mem_cons.mpr ⟨sound5089,List.forall_mem_cons.mpr ⟨sound5090,List.forall_mem_cons.mpr ⟨sound5091,List.forall_mem_cons.mpr ⟨sound5092,List.forall_mem_cons.mpr ⟨sound5093,List.forall_mem_cons.mpr ⟨sound5094,List.forall_mem_cons.mpr ⟨sound5095,List.forall_mem_cons.mpr ⟨sound5096,List.forall_mem_cons.mpr ⟨sound5097,List.forall_mem_cons.mpr ⟨sound5098,List.forall_mem_cons.mpr ⟨sound5099,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch424
