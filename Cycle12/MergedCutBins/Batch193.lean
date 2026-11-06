import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch357
import Cycle12.MergedCutProfiles.Batch358
import Cycle12.MergedCutProfiles.Batch359

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch193

def retention2316 : RatCutRetentionCertificate := ⟨(41/1000),(21/500),(1/2),(14104146669416203549/500000000000000000),1,(28000293028382304216135142768655010363/28208293338832407098000000000000000000),false,MergedCutProfiles.Batch357.profile14283,(fun _ => MergedCutProfiles.Batch357.profile14283)⟩
theorem profilesValid2316 : retention2316.ProfilesValid := by
  exact MergedCutProfiles.Batch357.valid14283
theorem numericValid2316 : retention2316.NumericValid := by decide +kernel
def certificate2316 : RatCutBinCertificate := ⟨⟨retention2316,(2357190291703044549/1000000000000000000),(81190354661587239/1000000000000000000),(11528565833256828971/1000000000000000000),(131085861669213648269/200000000000000000),(488012798801135901/500000000000000000)⟩,(498339811742589401/500000000000000000),(247161994640673137/1000000000000000000),(407285634558672929/1000000000000000000),(3063433747139137/8000000000000000)⟩
theorem valid2316 : certificate2316.Valid := by decide +kernel
theorem sound2316 : certificate2316.Sound := rat_cut_bin_certificate_sound certificate2316 profilesValid2316 numericValid2316 valid2316

def retention2317 : RatCutRetentionCertificate := ⟨(21/500),(43/1000),(788192692130023582/53651691046898568089),(780388804089132259/1000000000000000000),(67/20),(11121183766771316203/5000000000000000000),true,MergedCutProfiles.Batch357.profile14287,![MergedCutProfiles.Batch357.profile14287,MergedCutProfiles.Batch357.profile14288,MergedCutProfiles.Batch357.profile14289,MergedCutProfiles.Batch357.profile14290,MergedCutProfiles.Batch357.profile14291,MergedCutProfiles.Batch357.profile14292,MergedCutProfiles.Batch357.profile14293,MergedCutProfiles.Batch357.profile14294,MergedCutProfiles.Batch357.profile14295,MergedCutProfiles.Batch357.profile14296,MergedCutProfiles.Batch357.profile14297,MergedCutProfiles.Batch357.profile14298,MergedCutProfiles.Batch357.profile14299,MergedCutProfiles.Batch357.profile14300,MergedCutProfiles.Batch357.profile14301,MergedCutProfiles.Batch357.profile14302]⟩
theorem profilesValid2317 : retention2317.ProfilesValid := by
  change ∀ j : Fin 16, (retention2317.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch357.valid14287
  · exact MergedCutProfiles.Batch357.valid14288
  · exact MergedCutProfiles.Batch357.valid14289
  · exact MergedCutProfiles.Batch357.valid14290
  · exact MergedCutProfiles.Batch357.valid14291
  · exact MergedCutProfiles.Batch357.valid14292
  · exact MergedCutProfiles.Batch357.valid14293
  · exact MergedCutProfiles.Batch357.valid14294
  · exact MergedCutProfiles.Batch357.valid14295
  · exact MergedCutProfiles.Batch357.valid14296
  · exact MergedCutProfiles.Batch357.valid14297
  · exact MergedCutProfiles.Batch357.valid14298
  · exact MergedCutProfiles.Batch357.valid14299
  · exact MergedCutProfiles.Batch357.valid14300
  · exact MergedCutProfiles.Batch357.valid14301
  · exact MergedCutProfiles.Batch357.valid14302
theorem numericValid2317 : retention2317.NumericValid := by decide +kernel
def certificate2317 : RatCutBinCertificate := ⟨⟨retention2317,(1035870269245703707/500000000000000000),(21376650541548341/250000000000000000),(5854477843324358713/500000000000000000),(2526581676441047349/4000000000000000),(2173551205473791373/1000000000000000000)⟩,(498492787966605861/500000000000000000),(203194146608779063/500000000000000000),(113839905071803683/500000000000000000),(294829860421541/2500000000000000)⟩
theorem valid2317 : certificate2317.Valid := by decide +kernel
theorem sound2317 : certificate2317.Sound := rat_cut_bin_certificate_sound certificate2317 profilesValid2317 numericValid2317 valid2317

def retention2318 : RatCutRetentionCertificate := ⟨(21/500),(43/1000),(924217918876584955/53651691046898568089),(394096346065011791/500000000000000000),(67/20),(1418215169629470373799/640000000000000000000),true,MergedCutProfiles.Batch357.profile14303,![MergedCutProfiles.Batch357.profile14303,MergedCutProfiles.Batch357.profile14304,MergedCutProfiles.Batch357.profile14305,MergedCutProfiles.Batch357.profile14306,MergedCutProfiles.Batch357.profile14307,MergedCutProfiles.Batch357.profile14293,MergedCutProfiles.Batch357.profile14308,MergedCutProfiles.Batch357.profile14309,MergedCutProfiles.Batch357.profile14310,MergedCutProfiles.Batch357.profile14311,MergedCutProfiles.Batch357.profile14312,MergedCutProfiles.Batch357.profile14300,MergedCutProfiles.Batch357.profile14313,MergedCutProfiles.Batch357.profile14314,MergedCutProfiles.Batch357.profile14315,MergedCutProfiles.Batch357.profile14316]⟩
theorem profilesValid2318 : retention2318.ProfilesValid := by
  change ∀ j : Fin 16, (retention2318.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch357.valid14303
  · exact MergedCutProfiles.Batch357.valid14304
  · exact MergedCutProfiles.Batch357.valid14305
  · exact MergedCutProfiles.Batch357.valid14306
  · exact MergedCutProfiles.Batch357.valid14307
  · exact MergedCutProfiles.Batch357.valid14293
  · exact MergedCutProfiles.Batch357.valid14308
  · exact MergedCutProfiles.Batch357.valid14309
  · exact MergedCutProfiles.Batch357.valid14310
  · exact MergedCutProfiles.Batch357.valid14311
  · exact MergedCutProfiles.Batch357.valid14312
  · exact MergedCutProfiles.Batch357.valid14300
  · exact MergedCutProfiles.Batch357.valid14313
  · exact MergedCutProfiles.Batch357.valid14314
  · exact MergedCutProfiles.Batch357.valid14315
  · exact MergedCutProfiles.Batch357.valid14316
theorem numericValid2318 : retention2318.NumericValid := by decide +kernel
def certificate2318 : RatCutBinCertificate := ⟨⟨retention2318,(1035870269245703707/500000000000000000),(21376650541548341/250000000000000000),(5854477843324358713/500000000000000000),(2526581676441047349/4000000000000000),(1082637840324929513/500000000000000000)⟩,(498492787966605861/500000000000000000),(25370273378980153/62500000000000000),(7128056046028573/31250000000000000),(118019861639706123/1000000000000000000)⟩
theorem valid2318 : certificate2318.Valid := by decide +kernel
theorem sound2318 : certificate2318.Sound := rat_cut_bin_certificate_sound certificate2318 profilesValid2318 numericValid2318 valid2318

def retention2319 : RatCutRetentionCertificate := ⟨(21/500),(43/1000),(1048612652000000000/53651691046898568089),(184843583775316991/200000000000000000),(29/10),(35066897054394685757/16000000000000000000),true,MergedCutProfiles.Batch357.profile14317,![MergedCutProfiles.Batch357.profile14317,MergedCutProfiles.Batch357.profile14318,MergedCutProfiles.Batch357.profile14319,MergedCutProfiles.Batch358.profile14320,MergedCutProfiles.Batch358.profile14321,MergedCutProfiles.Batch357.profile14294,MergedCutProfiles.Batch358.profile14322,MergedCutProfiles.Batch358.profile14323,MergedCutProfiles.Batch357.profile14298,MergedCutProfiles.Batch358.profile14324,MergedCutProfiles.Batch358.profile14325,MergedCutProfiles.Batch358.profile14326,MergedCutProfiles.Batch358.profile14327,MergedCutProfiles.Batch358.profile14328,MergedCutProfiles.Batch358.profile14329,MergedCutProfiles.Batch358.profile14330]⟩
theorem profilesValid2319 : retention2319.ProfilesValid := by
  change ∀ j : Fin 16, (retention2319.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch357.valid14317
  · exact MergedCutProfiles.Batch357.valid14318
  · exact MergedCutProfiles.Batch357.valid14319
  · exact MergedCutProfiles.Batch358.valid14320
  · exact MergedCutProfiles.Batch358.valid14321
  · exact MergedCutProfiles.Batch357.valid14294
  · exact MergedCutProfiles.Batch358.valid14322
  · exact MergedCutProfiles.Batch358.valid14323
  · exact MergedCutProfiles.Batch357.valid14298
  · exact MergedCutProfiles.Batch358.valid14324
  · exact MergedCutProfiles.Batch358.valid14325
  · exact MergedCutProfiles.Batch358.valid14326
  · exact MergedCutProfiles.Batch358.valid14327
  · exact MergedCutProfiles.Batch358.valid14328
  · exact MergedCutProfiles.Batch358.valid14329
  · exact MergedCutProfiles.Batch358.valid14330
theorem numericValid2319 : retention2319.NumericValid := by decide +kernel
def certificate2319 : RatCutBinCertificate := ⟨⟨retention2319,(1035870269245703707/500000000000000000),(21376650541548341/250000000000000000),(5854477843324358713/500000000000000000),(2526581676441047349/4000000000000000),(1073902040167774503/500000000000000000)⟩,(498492787966605861/500000000000000000),(94824355163561943/250000000000000000),(63249007595952491/250000000000000000),(18286406346955773/125000000000000000)⟩
theorem valid2319 : certificate2319.Valid := by decide +kernel
theorem sound2319 : certificate2319.Sound := rat_cut_bin_certificate_sound certificate2319 profilesValid2319 numericValid2319 valid2319

def retention2320 : RatCutRetentionCertificate := ⟨(21/500),(43/1000),(1348921224730641839/53651691046898568089),(262153163/250000000),(13/5),(34505211336058208317/16000000000000000000),true,MergedCutProfiles.Batch358.profile14331,![MergedCutProfiles.Batch358.profile14331,MergedCutProfiles.Batch358.profile14332,MergedCutProfiles.Batch358.profile14333,MergedCutProfiles.Batch358.profile14334,MergedCutProfiles.Batch358.profile14335,MergedCutProfiles.Batch358.profile14336,MergedCutProfiles.Batch357.profile14298,MergedCutProfiles.Batch358.profile14337,MergedCutProfiles.Batch358.profile14338,MergedCutProfiles.Batch358.profile14339,MergedCutProfiles.Batch358.profile14340,MergedCutProfiles.Batch358.profile14341,MergedCutProfiles.Batch358.profile14342,MergedCutProfiles.Batch358.profile14343,MergedCutProfiles.Batch358.profile14344,MergedCutProfiles.Batch358.profile14345]⟩
theorem profilesValid2320 : retention2320.ProfilesValid := by
  change ∀ j : Fin 16, (retention2320.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch358.valid14331
  · exact MergedCutProfiles.Batch358.valid14332
  · exact MergedCutProfiles.Batch358.valid14333
  · exact MergedCutProfiles.Batch358.valid14334
  · exact MergedCutProfiles.Batch358.valid14335
  · exact MergedCutProfiles.Batch358.valid14336
  · exact MergedCutProfiles.Batch357.valid14298
  · exact MergedCutProfiles.Batch358.valid14337
  · exact MergedCutProfiles.Batch358.valid14338
  · exact MergedCutProfiles.Batch358.valid14339
  · exact MergedCutProfiles.Batch358.valid14340
  · exact MergedCutProfiles.Batch358.valid14341
  · exact MergedCutProfiles.Batch358.valid14342
  · exact MergedCutProfiles.Batch358.valid14343
  · exact MergedCutProfiles.Batch358.valid14344
  · exact MergedCutProfiles.Batch358.valid14345
theorem numericValid2320 : retention2320.NumericValid := by decide +kernel
def certificate2320 : RatCutBinCertificate := ⟨⟨retention2320,(1035870269245703707/500000000000000000),(21376650541548341/250000000000000000),(5854477843324358713/500000000000000000),(2526581676441047349/4000000000000000),(1058618877542078439/500000000000000000)⟩,(498492787966605861/500000000000000000),(22743972077273981/62500000000000000),(53646932515037793/200000000000000000),(8380234865036793/50000000000000000)⟩
theorem valid2320 : certificate2320.Valid := by decide +kernel
theorem sound2320 : certificate2320.Sound := rat_cut_bin_certificate_sound certificate2320 profilesValid2320 numericValid2320 valid2320

def retention2321 : RatCutRetentionCertificate := ⟨(21/500),(43/1000),(5709338422084309956/53651691046898568089),(1348921224730641839/1000000000000000000),(43/20),(2402473891015962866783/1280000000000000000000),true,MergedCutProfiles.Batch358.profile14346,![MergedCutProfiles.Batch358.profile14346,MergedCutProfiles.Batch358.profile14347,MergedCutProfiles.Batch358.profile14348,MergedCutProfiles.Batch358.profile14349,MergedCutProfiles.Batch358.profile14350,MergedCutProfiles.Batch358.profile14351,MergedCutProfiles.Batch358.profile14352,MergedCutProfiles.Batch358.profile14353,MergedCutProfiles.Batch358.profile14354,MergedCutProfiles.Batch358.profile14355,MergedCutProfiles.Batch358.profile14356,MergedCutProfiles.Batch358.profile14357,MergedCutProfiles.Batch358.profile14358,MergedCutProfiles.Batch358.profile14359,MergedCutProfiles.Batch359.profile14360,MergedCutProfiles.Batch359.profile14361]⟩
theorem profilesValid2321 : retention2321.ProfilesValid := by
  change ∀ j : Fin 16, (retention2321.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch358.valid14346
  · exact MergedCutProfiles.Batch358.valid14347
  · exact MergedCutProfiles.Batch358.valid14348
  · exact MergedCutProfiles.Batch358.valid14349
  · exact MergedCutProfiles.Batch358.valid14350
  · exact MergedCutProfiles.Batch358.valid14351
  · exact MergedCutProfiles.Batch358.valid14352
  · exact MergedCutProfiles.Batch358.valid14353
  · exact MergedCutProfiles.Batch358.valid14354
  · exact MergedCutProfiles.Batch358.valid14355
  · exact MergedCutProfiles.Batch358.valid14356
  · exact MergedCutProfiles.Batch358.valid14357
  · exact MergedCutProfiles.Batch358.valid14358
  · exact MergedCutProfiles.Batch358.valid14359
  · exact MergedCutProfiles.Batch359.valid14360
  · exact MergedCutProfiles.Batch359.valid14361
theorem numericValid2321 : retention2321.NumericValid := by decide +kernel
def certificate2321 : RatCutBinCertificate := ⟨⟨retention2321,(1035870269245703707/500000000000000000),(21376650541548341/250000000000000000),(5854477843324358713/500000000000000000),(2526581676441047349/4000000000000000),(184440336265509063/100000000000000000)⟩,(498492787966605861/500000000000000000),(378107814292985561/1000000000000000000),(254151054637445001/1000000000000000000),(167672743401216001/1000000000000000000)⟩
theorem valid2321 : certificate2321.Valid := by decide +kernel
theorem sound2321 : certificate2321.Sound := rat_cut_bin_certificate_sound certificate2321 profilesValid2321 numericValid2321 valid2321

def retention2322 : RatCutRetentionCertificate := ⟨(21/500),(43/1000),(22764428007567025366/53651691046898568089),(1427334605521077489/250000000000000000),(11/10),(162679455645560417205898027788195111599/142733460552107748900000000000000000000),false,MergedCutProfiles.Batch359.profile14362,(fun _ => MergedCutProfiles.Batch359.profile14362)⟩
theorem profilesValid2322 : retention2322.ProfilesValid := by
  exact MergedCutProfiles.Batch359.valid14362
theorem numericValid2322 : retention2322.NumericValid := by decide +kernel
def certificate2322 : RatCutBinCertificate := ⟨⟨retention2322,(1035870269245703707/500000000000000000),(21376650541548341/250000000000000000),(5854477843324358713/500000000000000000),(2526581676441047349/4000000000000000),(561550219535449/500000000000000)⟩,(498492787966605861/500000000000000000),(223700043955823337/500000000000000000),(96377403992142187/500000000000000000),(16873198529518483/100000000000000000)⟩
theorem valid2322 : certificate2322.Valid := by decide +kernel
theorem sound2322 : certificate2322.Sound := rat_cut_bin_certificate_sound certificate2322 profilesValid2322 numericValid2322 valid2322

def retention2323 : RatCutRetentionCertificate := ⟨(21/500),(43/1000),(26428794203540626557/53651691046898568089),(11382214003783512683/500000000000000000),1,(5719627618315521336466992508200415893/5691107001891756341500000000000000000),false,MergedCutProfiles.Batch359.profile14363,(fun _ => MergedCutProfiles.Batch359.profile14363)⟩
theorem profilesValid2323 : retention2323.ProfilesValid := by
  exact MergedCutProfiles.Batch359.valid14363
theorem numericValid2323 : retention2323.NumericValid := by decide +kernel
def certificate2323 : RatCutBinCertificate := ⟨⟨retention2323,(1035870269245703707/500000000000000000),(21376650541548341/250000000000000000),(5854477843324358713/500000000000000000),(2526581676441047349/4000000000000000),(989882114779994341/1000000000000000000)⟩,(498492787966605861/500000000000000000),(230987876049107849/500000000000000000),(45316644389533609/250000000000000000),(171424504183790951/1000000000000000000)⟩
theorem valid2323 : certificate2323.Valid := by decide +kernel
theorem sound2323 : certificate2323.Sound := rat_cut_bin_certificate_sound certificate2323 profilesValid2323 numericValid2323 valid2323

def retention2324 : RatCutRetentionCertificate := ⟨(21/500),(43/1000),(26693082145576032823/53651691046898568089),(26428794203540626557/1000000000000000000),1,(105386949784614088455971879951319279971/105715176814162506228000000000000000000),false,MergedCutProfiles.Batch359.profile14364,(fun _ => MergedCutProfiles.Batch359.profile14364)⟩
theorem profilesValid2324 : retention2324.ProfilesValid := by
  exact MergedCutProfiles.Batch359.valid14364
theorem numericValid2324 : retention2324.NumericValid := by decide +kernel
def certificate2324 : RatCutBinCertificate := ⟨⟨retention2324,(1035870269245703707/500000000000000000),(21376650541548341/250000000000000000),(5854477843324358713/500000000000000000),(2526581676441047349/4000000000000000),(981765867512536433/1000000000000000000)⟩,(498492787966605861/500000000000000000),(463659245661135807/1000000000000000000),(17996958562217447/100000000000000000),(33967067385354049/200000000000000000)⟩
theorem valid2324 : certificate2324.Valid := by decide +kernel
theorem sound2324 : certificate2324.Sound := rat_cut_bin_certificate_sound certificate2324 profilesValid2324 numericValid2324 valid2324

def retention2325 : RatCutRetentionCertificate := ⟨(21/500),(43/1000),(1/2),(26693082145576032823/1000000000000000000),1,(26482881956047593879477999161965269453/26693082145576032823000000000000000000),false,MergedCutProfiles.Batch359.profile14365,(fun _ => MergedCutProfiles.Batch359.profile14365)⟩
theorem profilesValid2325 : retention2325.ProfilesValid := by
  exact MergedCutProfiles.Batch359.valid14365
theorem numericValid2325 : retention2325.NumericValid := by decide +kernel
def certificate2325 : RatCutBinCertificate := ⟨⟨retention2325,(1035870269245703707/500000000000000000),(21376650541548341/250000000000000000),(5854477843324358713/500000000000000000),(2526581676441047349/4000000000000000),(97699598581088577/100000000000000000)⟩,(498492787966605861/500000000000000000),(465790916323303633/1000000000000000000),(178336076997152857/1000000000000000000),(33512910677141097/200000000000000000)⟩
theorem valid2325 : certificate2325.Valid := by decide +kernel
theorem sound2325 : certificate2325.Sound := rat_cut_bin_certificate_sound certificate2325 profilesValid2325 numericValid2325 valid2325

def retention2326 : RatCutRetentionCertificate := ⟨(21/500),(43/1000),(23549880597217746595/53651691046898568089),(561967092213826061/100000000000000000),(21/20),(98286306979862180551362809141207317439/89914734754212169760000000000000000000),false,MergedCutProfiles.Batch359.profile14366,(fun _ => MergedCutProfiles.Batch359.profile14366)⟩
theorem profilesValid2326 : retention2326.ProfilesValid := by
  exact MergedCutProfiles.Batch359.valid14366
theorem numericValid2326 : retention2326.NumericValid := by decide +kernel
def certificate2326 : RatCutBinCertificate := ⟨⟨retention2326,(1181585897745703707/500000000000000000),(21376650541548341/250000000000000000),(5854477843324358713/500000000000000000),(2526581676441047349/4000000000000000),(53749246596558437/50000000000000000)⟩,(4982807043823873/5000000000000000),(44435419788706471/200000000000000000),(221717457289080527/500000000000000000),(77087477087322307/200000000000000000)⟩
theorem valid2326 : certificate2326.Valid := by decide +kernel
theorem sound2326 : certificate2326.Sound := rat_cut_bin_certificate_sound certificate2326 profilesValid2326 numericValid2326 valid2326

def retention2327 : RatCutRetentionCertificate := ⟨(21/500),(43/1000),(26536594913564176393/53651691046898568089),(4709976119443549319/200000000000000000),1,(94335736496249061669588255554283669219/94199522388870986380000000000000000000),false,MergedCutProfiles.Batch359.profile14367,(fun _ => MergedCutProfiles.Batch359.profile14367)⟩
theorem profilesValid2327 : retention2327.ProfilesValid := by
  exact MergedCutProfiles.Batch359.valid14367
theorem numericValid2327 : retention2327.NumericValid := by decide +kernel
def certificate2327 : RatCutBinCertificate := ⟨⟨retention2327,(1181585897745703707/500000000000000000),(21376650541548341/250000000000000000),(5854477843324358713/500000000000000000),(2526581676441047349/4000000000000000),(492094230753636891/500000000000000000)⟩,(4982807043823873/5000000000000000),(242674084208121467/1000000000000000000),(206794204290660681/500000000000000000),(389349214151715153/1000000000000000000)⟩
theorem valid2327 : certificate2327.Valid := by decide +kernel
theorem sound2327 : certificate2327.Sound := rat_cut_bin_certificate_sound certificate2327 profilesValid2327 numericValid2327 valid2327

def certificates : List RatCutBinCertificate := [certificate2316,certificate2317,certificate2318,certificate2319,certificate2320,certificate2321,certificate2322,certificate2323,certificate2324,certificate2325,certificate2326,certificate2327]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound2316,List.forall_mem_cons.mpr ⟨sound2317,List.forall_mem_cons.mpr ⟨sound2318,List.forall_mem_cons.mpr ⟨sound2319,List.forall_mem_cons.mpr ⟨sound2320,List.forall_mem_cons.mpr ⟨sound2321,List.forall_mem_cons.mpr ⟨sound2322,List.forall_mem_cons.mpr ⟨sound2323,List.forall_mem_cons.mpr ⟨sound2324,List.forall_mem_cons.mpr ⟨sound2325,List.forall_mem_cons.mpr ⟨sound2326,List.forall_mem_cons.mpr ⟨sound2327,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch193
