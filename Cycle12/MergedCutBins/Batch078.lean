import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch157
import Cycle12.MergedCutProfiles.Batch158
import Cycle12.MergedCutProfiles.Batch159

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch078

def retention936 : RatCutRetentionCertificate := ⟨(101/2000),(203/4000),(280511516648387887/6146097064611291546),(416601262349090921/500000000000000000),(59/20),(1327064212253115778313/640000000000000000000),true,MergedCutProfiles.Batch157.profile6284,![MergedCutProfiles.Batch157.profile6284,MergedCutProfiles.Batch157.profile6285,MergedCutProfiles.Batch157.profile6286,MergedCutProfiles.Batch157.profile6287,MergedCutProfiles.Batch157.profile6288,MergedCutProfiles.Batch157.profile6289,MergedCutProfiles.Batch157.profile6290,MergedCutProfiles.Batch157.profile6291,MergedCutProfiles.Batch157.profile6292,MergedCutProfiles.Batch157.profile6293,MergedCutProfiles.Batch157.profile6294,MergedCutProfiles.Batch157.profile6295,MergedCutProfiles.Batch157.profile6296,MergedCutProfiles.Batch157.profile6297,MergedCutProfiles.Batch157.profile6298,MergedCutProfiles.Batch157.profile6299]⟩
theorem profilesValid936 : retention936.ProfilesValid := by
  change ∀ j : Fin 16, (retention936.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch157.valid6284
  · exact MergedCutProfiles.Batch157.valid6285
  · exact MergedCutProfiles.Batch157.valid6286
  · exact MergedCutProfiles.Batch157.valid6287
  · exact MergedCutProfiles.Batch157.valid6288
  · exact MergedCutProfiles.Batch157.valid6289
  · exact MergedCutProfiles.Batch157.valid6290
  · exact MergedCutProfiles.Batch157.valid6291
  · exact MergedCutProfiles.Batch157.valid6292
  · exact MergedCutProfiles.Batch157.valid6293
  · exact MergedCutProfiles.Batch157.valid6294
  · exact MergedCutProfiles.Batch157.valid6295
  · exact MergedCutProfiles.Batch157.valid6296
  · exact MergedCutProfiles.Batch157.valid6297
  · exact MergedCutProfiles.Batch157.valid6298
  · exact MergedCutProfiles.Batch157.valid6299
theorem numericValid936 : retention936.NumericValid := by decide +kernel
def certificate936 : RatCutBinCertificate := ⟨⟨retention936,(2170590876793678081/1000000000000000000),(15480000080526917/125000000000000000),(6715899248821398269/500000000000000000),(2480156854086673507/10000000000000000),(2014488500412648871/1000000000000000000)⟩,(992311453406067763/1000000000000000000),(75837904461583597/200000000000000000),(253100638192309391/1000000000000000000),(67011982398241637/500000000000000000)⟩
theorem valid936 : certificate936.Valid := by decide +kernel
theorem sound936 : certificate936.Sound := rat_cut_bin_certificate_sound certificate936 profilesValid936 numericValid936 valid936

def retention937 : RatCutRetentionCertificate := ⟨(101/2000),(203/4000),(455630665212914480/9219145596916937319),(841534549945163661/1000000000000000000),(29/10),(2633418314919636877361/1280000000000000000000),true,MergedCutProfiles.Batch157.profile6300,![MergedCutProfiles.Batch157.profile6300,MergedCutProfiles.Batch157.profile6301,MergedCutProfiles.Batch157.profile6302,MergedCutProfiles.Batch157.profile6303,MergedCutProfiles.Batch157.profile6304,MergedCutProfiles.Batch157.profile6305,MergedCutProfiles.Batch157.profile6306,MergedCutProfiles.Batch157.profile6307,MergedCutProfiles.Batch157.profile6308,MergedCutProfiles.Batch157.profile6309,MergedCutProfiles.Batch157.profile6310,MergedCutProfiles.Batch157.profile6296,MergedCutProfiles.Batch157.profile6311,MergedCutProfiles.Batch157.profile6312,MergedCutProfiles.Batch157.profile6313,MergedCutProfiles.Batch157.profile6314]⟩
theorem profilesValid937 : retention937.ProfilesValid := by
  change ∀ j : Fin 16, (retention937.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch157.valid6300
  · exact MergedCutProfiles.Batch157.valid6301
  · exact MergedCutProfiles.Batch157.valid6302
  · exact MergedCutProfiles.Batch157.valid6303
  · exact MergedCutProfiles.Batch157.valid6304
  · exact MergedCutProfiles.Batch157.valid6305
  · exact MergedCutProfiles.Batch157.valid6306
  · exact MergedCutProfiles.Batch157.valid6307
  · exact MergedCutProfiles.Batch157.valid6308
  · exact MergedCutProfiles.Batch157.valid6309
  · exact MergedCutProfiles.Batch157.valid6310
  · exact MergedCutProfiles.Batch157.valid6296
  · exact MergedCutProfiles.Batch157.valid6311
  · exact MergedCutProfiles.Batch157.valid6312
  · exact MergedCutProfiles.Batch157.valid6313
  · exact MergedCutProfiles.Batch157.valid6314
theorem numericValid937 : retention937.NumericValid := by decide +kernel
def certificate937 : RatCutBinCertificate := ⟨⟨retention937,(2170590876793678081/1000000000000000000),(15480000080526917/125000000000000000),(6715899248821398269/500000000000000000),(2480156854086673507/10000000000000000),(249913684861314539/125000000000000000)⟩,(992311453406067763/1000000000000000000),(380507363422430767/1000000000000000000),(62956271270548589/250000000000000000),(13413447648974997/100000000000000000)⟩
theorem valid937 : certificate937.Valid := by decide +kernel
theorem sound937 : certificate937.Sound := rat_cut_bin_certificate_sound certificate937 profilesValid937 numericValid937 valid937

def retention938 : RatCutRetentionCertificate := ⟨(101/2000),(203/4000),(1454613149006077609/18438291193833874638),(5695383315161431/6250000000000000),(27/10),(15711040967813925889/8000000000000000000),true,MergedCutProfiles.Batch157.profile6315,![MergedCutProfiles.Batch157.profile6315,MergedCutProfiles.Batch157.profile6316,MergedCutProfiles.Batch157.profile6317,MergedCutProfiles.Batch157.profile6318,MergedCutProfiles.Batch157.profile6307,MergedCutProfiles.Batch157.profile6319,MergedCutProfiles.Batch158.profile6320,MergedCutProfiles.Batch158.profile6321,MergedCutProfiles.Batch158.profile6322,MergedCutProfiles.Batch158.profile6323,MergedCutProfiles.Batch158.profile6324,MergedCutProfiles.Batch158.profile6325,MergedCutProfiles.Batch158.profile6326,MergedCutProfiles.Batch158.profile6327,MergedCutProfiles.Batch158.profile6328,MergedCutProfiles.Batch158.profile6329]⟩
theorem profilesValid938 : retention938.ProfilesValid := by
  change ∀ j : Fin 16, (retention938.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch157.valid6315
  · exact MergedCutProfiles.Batch157.valid6316
  · exact MergedCutProfiles.Batch157.valid6317
  · exact MergedCutProfiles.Batch157.valid6318
  · exact MergedCutProfiles.Batch157.valid6307
  · exact MergedCutProfiles.Batch157.valid6319
  · exact MergedCutProfiles.Batch158.valid6320
  · exact MergedCutProfiles.Batch158.valid6321
  · exact MergedCutProfiles.Batch158.valid6322
  · exact MergedCutProfiles.Batch158.valid6323
  · exact MergedCutProfiles.Batch158.valid6324
  · exact MergedCutProfiles.Batch158.valid6325
  · exact MergedCutProfiles.Batch158.valid6326
  · exact MergedCutProfiles.Batch158.valid6327
  · exact MergedCutProfiles.Batch158.valid6328
  · exact MergedCutProfiles.Batch158.valid6329
theorem numericValid938 : retention938.NumericValid := by decide +kernel
def certificate938 : RatCutBinCertificate := ⟨⟨retention938,(2170590876793678081/1000000000000000000),(15480000080526917/125000000000000000),(6715899248821398269/500000000000000000),(2480156854086673507/10000000000000000),(29841171583181411/15625000000000000)⟩,(992311453406067763/1000000000000000000),(385829903517321697/1000000000000000000),(12335979313017003/50000000000000000),(134311805757033411/1000000000000000000)⟩
theorem valid938 : certificate938.Valid := by decide +kernel
theorem sound938 : certificate938.Sound := rat_cut_bin_certificate_sound certificate938 profilesValid938 numericValid938 valid938

def retention939 : RatCutRetentionCertificate := ⟨(101/2000),(203/4000),(1448696365093193309/6146097064611291546),(1454613149006077609/1000000000000000000),(19/10),(1986804940346813017493/1280000000000000000000),true,MergedCutProfiles.Batch158.profile6330,![MergedCutProfiles.Batch158.profile6330,MergedCutProfiles.Batch158.profile6331,MergedCutProfiles.Batch158.profile6332,MergedCutProfiles.Batch158.profile6333,MergedCutProfiles.Batch158.profile6334,MergedCutProfiles.Batch158.profile6335,MergedCutProfiles.Batch158.profile6336,MergedCutProfiles.Batch158.profile6337,MergedCutProfiles.Batch158.profile6338,MergedCutProfiles.Batch158.profile6339,MergedCutProfiles.Batch158.profile6340,MergedCutProfiles.Batch158.profile6341,MergedCutProfiles.Batch158.profile6342,MergedCutProfiles.Batch158.profile6343,MergedCutProfiles.Batch158.profile6344,MergedCutProfiles.Batch158.profile6345]⟩
theorem profilesValid939 : retention939.ProfilesValid := by
  change ∀ j : Fin 16, (retention939.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch158.valid6330
  · exact MergedCutProfiles.Batch158.valid6331
  · exact MergedCutProfiles.Batch158.valid6332
  · exact MergedCutProfiles.Batch158.valid6333
  · exact MergedCutProfiles.Batch158.valid6334
  · exact MergedCutProfiles.Batch158.valid6335
  · exact MergedCutProfiles.Batch158.valid6336
  · exact MergedCutProfiles.Batch158.valid6337
  · exact MergedCutProfiles.Batch158.valid6338
  · exact MergedCutProfiles.Batch158.valid6339
  · exact MergedCutProfiles.Batch158.valid6340
  · exact MergedCutProfiles.Batch158.valid6341
  · exact MergedCutProfiles.Batch158.valid6342
  · exact MergedCutProfiles.Batch158.valid6343
  · exact MergedCutProfiles.Batch158.valid6344
  · exact MergedCutProfiles.Batch158.valid6345
theorem numericValid939 : retention939.NumericValid := by decide +kernel
def certificate939 : RatCutBinCertificate := ⟨⟨retention939,(2170590876793678081/1000000000000000000),(15480000080526917/125000000000000000),(6715899248821398269/500000000000000000),(2480156854086673507/10000000000000000),(1514160441717274273/1000000000000000000)⟩,(992311453406067763/1000000000000000000),(103888023741169321/250000000000000000),(21953112280691409/100000000000000000),(134577674623535749/1000000000000000000)⟩
theorem valid939 : certificate939.Valid := by decide +kernel
theorem sound939 : certificate939.Sound := rat_cut_bin_certificate_sound certificate939 profilesValid939 numericValid939 valid939

def retention940 : RatCutRetentionCertificate := ⟨(101/2000),(203/4000),(4067384017815315019/9219145596916937319),(4346089095279579927/1000000000000000000),(21/20),(1382443646313390091743/1280000000000000000000),true,MergedCutProfiles.Batch158.profile6346,![MergedCutProfiles.Batch158.profile6346,MergedCutProfiles.Batch158.profile6347,MergedCutProfiles.Batch158.profile6348,MergedCutProfiles.Batch158.profile6349,MergedCutProfiles.Batch158.profile6350,MergedCutProfiles.Batch158.profile6351,MergedCutProfiles.Batch158.profile6352,MergedCutProfiles.Batch158.profile6353,MergedCutProfiles.Batch158.profile6354,MergedCutProfiles.Batch158.profile6355,MergedCutProfiles.Batch158.profile6356,MergedCutProfiles.Batch158.profile6357,MergedCutProfiles.Batch158.profile6358,MergedCutProfiles.Batch158.profile6359,MergedCutProfiles.Batch159.profile6360,MergedCutProfiles.Batch159.profile6361]⟩
theorem profilesValid940 : retention940.ProfilesValid := by
  change ∀ j : Fin 16, (retention940.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch158.valid6346
  · exact MergedCutProfiles.Batch158.valid6347
  · exact MergedCutProfiles.Batch158.valid6348
  · exact MergedCutProfiles.Batch158.valid6349
  · exact MergedCutProfiles.Batch158.valid6350
  · exact MergedCutProfiles.Batch158.valid6351
  · exact MergedCutProfiles.Batch158.valid6352
  · exact MergedCutProfiles.Batch158.valid6353
  · exact MergedCutProfiles.Batch158.valid6354
  · exact MergedCutProfiles.Batch158.valid6355
  · exact MergedCutProfiles.Batch158.valid6356
  · exact MergedCutProfiles.Batch158.valid6357
  · exact MergedCutProfiles.Batch158.valid6358
  · exact MergedCutProfiles.Batch158.valid6359
  · exact MergedCutProfiles.Batch159.valid6360
  · exact MergedCutProfiles.Batch159.valid6361
theorem numericValid940 : retention940.NumericValid := by decide +kernel
def certificate940 : RatCutBinCertificate := ⟨⟨retention940,(2170590876793678081/1000000000000000000),(15480000080526917/125000000000000000),(6715899248821398269/500000000000000000),(2480156854086673507/10000000000000000),(1059018509623684869/1000000000000000000)⟩,(992311453406067763/1000000000000000000),(58681220205189/122070312500000),(20896162625635361/125000000000000000),(6845599484739663/50000000000000000)⟩
theorem valid940 : certificate940.Valid := by decide +kernel
theorem sound940 : certificate940.Sound := rat_cut_bin_certificate_sound certificate940 profilesValid940 numericValid940 valid940

def retention941 : RatCutRetentionCertificate := ⟨(101/2000),(203/4000),(3025234401605963311/6146097064611291546),(4067384017815315019/500000000000000000),(21/20),(3272466175438660458534455899572352614119/3253907214252252015200000000000000000000),false,MergedCutProfiles.Batch159.profile6362,(fun _ => MergedCutProfiles.Batch159.profile6362)⟩
theorem profilesValid941 : retention941.ProfilesValid := by
  exact MergedCutProfiles.Batch159.valid6362
theorem numericValid941 : retention941.NumericValid := by decide +kernel
def certificate941 : RatCutBinCertificate := ⟨⟨retention941,(2170590876793678081/1000000000000000000),(15480000080526917/125000000000000000),(6715899248821398269/500000000000000000),(2480156854086673507/10000000000000000),(984689074420071077/1000000000000000000)⟩,(992311453406067763/1000000000000000000),(15263149166165631/31250000000000000),(3231751349270983/20000000000000000),(135429954835310929/1000000000000000000)⟩
theorem valid941 : certificate941.Valid := by decide +kernel
theorem sound941 : certificate941.Sound := rat_cut_bin_certificate_sound certificate941 profilesValid941 numericValid941 valid941

def retention942 : RatCutRetentionCertificate := ⟨(101/2000),(203/4000),(9166460236866068833/18438291193833874638),(9075703204817889933/1000000000000000000),(21/20),(4834773188168589170032046437651414920837/4840375042569541297600000000000000000000),false,MergedCutProfiles.Batch159.profile6363,(fun _ => MergedCutProfiles.Batch159.profile6363)⟩
theorem profilesValid942 : retention942.ProfilesValid := by
  exact MergedCutProfiles.Batch159.valid6363
theorem numericValid942 : retention942.NumericValid := by decide +kernel
def certificate942 : RatCutBinCertificate := ⟨⟨retention942,(2170590876793678081/1000000000000000000),(15480000080526917/125000000000000000),(6715899248821398269/500000000000000000),(2480156854086673507/10000000000000000),(244457072724205389/250000000000000000)⟩,(992311453406067763/1000000000000000000),(122106128519557043/250000000000000000),(80792443470412447/500000000000000000),(135968805100305087/1000000000000000000)⟩
theorem valid942 : certificate942.Valid := by decide +kernel
theorem sound942 : certificate942.Sound := rat_cut_bin_certificate_sound certificate942 profilesValid942 numericValid942 valid942

def retention943 : RatCutRetentionCertificate := ⟨(101/2000),(203/4000),(1/2),(9166460236866068833/1000000000000000000),(21/20),(14571115389714557193027359332946213990111/14666336378985710132800000000000000000000),false,MergedCutProfiles.Batch159.profile6364,(fun _ => MergedCutProfiles.Batch159.profile6364)⟩
theorem profilesValid943 : retention943.ProfilesValid := by
  exact MergedCutProfiles.Batch159.valid6364
theorem numericValid943 : retention943.NumericValid := by decide +kernel
def certificate943 : RatCutBinCertificate := ⟨⟨retention943,(2170590876793678081/1000000000000000000),(15480000080526917/125000000000000000),(6715899248821398269/500000000000000000),(2480156854086673507/10000000000000000),(194498626733613201/200000000000000000)⟩,(992311453406067763/1000000000000000000),(490809415043199947/1000000000000000000),(159881756828552851/1000000000000000000),(133984661735786177/1000000000000000000)⟩
theorem valid943 : certificate943.Valid := by decide +kernel
theorem sound943 : certificate943.Sound := rat_cut_bin_certificate_sound certificate943 profilesValid943 numericValid943 valid943

def retention944 : RatCutRetentionCertificate := ⟨(101/2000),(203/4000),(1/2),64,1,(25539520414378814930550893732019039/25600000000000000000000000000000000),false,MergedCutProfiles.Batch159.profile6364,(fun _ => MergedCutProfiles.Batch159.profile6364)⟩
theorem profilesValid944 : retention944.ProfilesValid := by
  exact MergedCutProfiles.Batch159.valid6364
theorem numericValid944 : retention944.NumericValid := by decide +kernel
def certificate944 : RatCutBinCertificate := ⟨⟨retention944,(2170590876793678081/1000000000000000000),(15480000080526917/125000000000000000),(6715899248821398269/500000000000000000),(2480156854086673507/10000000000000000),(488812351548749307/500000000000000000)⟩,(992311453406067763/1000000000000000000),(231561428000319353/500000000000000000),(180382164773626111/1000000000000000000),(43086322016982527/250000000000000000)⟩
theorem valid944 : certificate944.Valid := by decide +kernel
theorem sound944 : certificate944.Sound := rat_cut_bin_certificate_sound certificate944 profilesValid944 numericValid944 valid944

def retention945 : RatCutRetentionCertificate := ⟨(101/2000),(203/4000),(8361599891170128431/18438291193833874638),(3809788386246167301/1000000000000000000),(6/5),(414512702286029066222137551645311268239/380978838624616730100000000000000000000),false,MergedCutProfiles.Batch159.profile6365,(fun _ => MergedCutProfiles.Batch159.profile6365)⟩
theorem profilesValid945 : retention945.ProfilesValid := by
  exact MergedCutProfiles.Batch159.valid6365
theorem numericValid945 : retention945.NumericValid := by decide +kernel
def certificate945 : RatCutBinCertificate := ⟨⟨retention945,(2546767058793678081/1000000000000000000),(15480000080526917/125000000000000000),(6715899248821398269/500000000000000000),(2480156854086673507/10000000000000000),(1059840039576086293/1000000000000000000)⟩,(495488652841187767/500000000000000000),(376761838296518517/1000000000000000000),(3991600200984897/15625000000000000),(18723106180813707/100000000000000000)⟩
theorem valid945 : certificate945.Valid := by decide +kernel
theorem sound945 : certificate945.Sound := rat_cut_bin_certificate_sound certificate945 profilesValid945 numericValid945 valid945

def retention946 : RatCutRetentionCertificate := ⟨(101/2000),(203/4000),(4572479328525962176/9219145596916937319),(8361599891170128431/1000000000000000000),(21/20),(13367288348191690189448271373009193419079/13378559825872205489600000000000000000000),false,MergedCutProfiles.Batch159.profile6366,(fun _ => MergedCutProfiles.Batch159.profile6366)⟩
theorem profilesValid946 : retention946.ProfilesValid := by
  exact MergedCutProfiles.Batch159.valid6366
theorem numericValid946 : retention946.NumericValid := by decide +kernel
def certificate946 : RatCutBinCertificate := ⟨⟨retention946,(2546767058793678081/1000000000000000000),(15480000080526917/125000000000000000),(6715899248821398269/500000000000000000),(2480156854086673507/10000000000000000),(974501078065054813/1000000000000000000)⟩,(495488652841187767/500000000000000000),(204877803934191561/500000000000000000),(224661745347447347/1000000000000000000),(37356869451111347/200000000000000000)⟩
theorem valid946 : certificate946.Valid := by decide +kernel
theorem sound946 : certificate946.Sound := rat_cut_bin_certificate_sound certificate946 profilesValid946 numericValid946 valid946

def retention947 : RatCutRetentionCertificate := ⟨(101/2000),(203/4000),(1/2),(71444989508218159/7812500000000000),(21/20),(56781998660481682181241507715524808391/57155991606574527200000000000000000000),false,MergedCutProfiles.Batch159.profile6364,(fun _ => MergedCutProfiles.Batch159.profile6364)⟩
theorem profilesValid947 : retention947.ProfilesValid := by
  exact MergedCutProfiles.Batch159.valid6364
theorem numericValid947 : retention947.NumericValid := by decide +kernel
def certificate947 : RatCutBinCertificate := ⟨⟨retention947,(2546767058793678081/1000000000000000000),(15480000080526917/125000000000000000),(6715899248821398269/500000000000000000),(2480156854086673507/10000000000000000),(193760065740380393/200000000000000000)⟩,(495488652841187767/500000000000000000),(412166748690077403/1000000000000000000),(222517690570290361/1000000000000000000),(3710811825157819/20000000000000000)⟩
theorem valid947 : certificate947.Valid := by decide +kernel
theorem sound947 : certificate947.Sound := rat_cut_bin_certificate_sound certificate947 profilesValid947 numericValid947 valid947

def certificates : List RatCutBinCertificate := [certificate936,certificate937,certificate938,certificate939,certificate940,certificate941,certificate942,certificate943,certificate944,certificate945,certificate946,certificate947]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound936,List.forall_mem_cons.mpr ⟨sound937,List.forall_mem_cons.mpr ⟨sound938,List.forall_mem_cons.mpr ⟨sound939,List.forall_mem_cons.mpr ⟨sound940,List.forall_mem_cons.mpr ⟨sound941,List.forall_mem_cons.mpr ⟨sound942,List.forall_mem_cons.mpr ⟨sound943,List.forall_mem_cons.mpr ⟨sound944,List.forall_mem_cons.mpr ⟨sound945,List.forall_mem_cons.mpr ⟨sound946,List.forall_mem_cons.mpr ⟨sound947,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch078
