import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch380
import Cycle12.MergedCutProfiles.Batch381
import Cycle12.MergedCutProfiles.Batch382

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch204

def retention2448 : RatCutRetentionCertificate := ⟨(13/250),(53/1000),(864574383039863601/33373862222675650447),(856014240633528317/1000000000000000000),3,(34606803211846877289/16000000000000000000),true,MergedCutProfiles.Batch380.profile15215,![MergedCutProfiles.Batch380.profile15215,MergedCutProfiles.Batch380.profile15216,MergedCutProfiles.Batch380.profile15217,MergedCutProfiles.Batch380.profile15218,MergedCutProfiles.Batch380.profile15219,MergedCutProfiles.Batch380.profile15220,MergedCutProfiles.Batch380.profile15221,MergedCutProfiles.Batch380.profile15222,MergedCutProfiles.Batch380.profile15223,MergedCutProfiles.Batch380.profile15224,MergedCutProfiles.Batch380.profile15225,MergedCutProfiles.Batch380.profile15226,MergedCutProfiles.Batch380.profile15227,MergedCutProfiles.Batch380.profile15228,MergedCutProfiles.Batch380.profile15229,MergedCutProfiles.Batch380.profile15230]⟩
theorem profilesValid2448 : retention2448.ProfilesValid := by
  change ∀ j : Fin 16, (retention2448.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch380.valid15215
  · exact MergedCutProfiles.Batch380.valid15216
  · exact MergedCutProfiles.Batch380.valid15217
  · exact MergedCutProfiles.Batch380.valid15218
  · exact MergedCutProfiles.Batch380.valid15219
  · exact MergedCutProfiles.Batch380.valid15220
  · exact MergedCutProfiles.Batch380.valid15221
  · exact MergedCutProfiles.Batch380.valid15222
  · exact MergedCutProfiles.Batch380.valid15223
  · exact MergedCutProfiles.Batch380.valid15224
  · exact MergedCutProfiles.Batch380.valid15225
  · exact MergedCutProfiles.Batch380.valid15226
  · exact MergedCutProfiles.Batch380.valid15227
  · exact MergedCutProfiles.Batch380.valid15228
  · exact MergedCutProfiles.Batch380.valid15229
  · exact MergedCutProfiles.Batch380.valid15230
theorem numericValid2448 : retention2448.NumericValid := by decide +kernel
def certificate2448 : RatCutBinCertificate := ⟨⟨retention2448,(1090065047647843647/500000000000000000),(136712609017002193/1000000000000000000),(13778560094102840813/1000000000000000000),(462528081660201628653/1000000000000000000),(2098023155150228987/1000000000000000000)⟩,(995900866633824653/1000000000000000000),(87528881022739177/250000000000000000),(14121760137954941/50000000000000000),(154489275177975349/1000000000000000000)⟩
theorem valid2448 : certificate2448.Valid := by decide +kernel
theorem sound2448 : certificate2448.Sound := rat_cut_bin_certificate_sound certificate2448 profilesValid2448 numericValid2448 valid2448

def retention2449 : RatCutRetentionCertificate := ⟨(13/250),(53/1000),(964578272495270733/33373862222675650447),(864574383039863601/1000000000000000000),3,(110404298842603152629/51200000000000000000),true,MergedCutProfiles.Batch380.profile15231,![MergedCutProfiles.Batch380.profile15231,MergedCutProfiles.Batch380.profile15232,MergedCutProfiles.Batch380.profile15233,MergedCutProfiles.Batch380.profile15234,MergedCutProfiles.Batch380.profile15235,MergedCutProfiles.Batch380.profile15236,MergedCutProfiles.Batch380.profile15237,MergedCutProfiles.Batch380.profile15238,MergedCutProfiles.Batch380.profile15239,MergedCutProfiles.Batch381.profile15240,MergedCutProfiles.Batch381.profile15241,MergedCutProfiles.Batch381.profile15242,MergedCutProfiles.Batch381.profile15243,MergedCutProfiles.Batch381.profile15244,MergedCutProfiles.Batch381.profile15245,MergedCutProfiles.Batch381.profile15246]⟩
theorem profilesValid2449 : retention2449.ProfilesValid := by
  change ∀ j : Fin 16, (retention2449.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch380.valid15231
  · exact MergedCutProfiles.Batch380.valid15232
  · exact MergedCutProfiles.Batch380.valid15233
  · exact MergedCutProfiles.Batch380.valid15234
  · exact MergedCutProfiles.Batch380.valid15235
  · exact MergedCutProfiles.Batch380.valid15236
  · exact MergedCutProfiles.Batch380.valid15237
  · exact MergedCutProfiles.Batch380.valid15238
  · exact MergedCutProfiles.Batch380.valid15239
  · exact MergedCutProfiles.Batch381.valid15240
  · exact MergedCutProfiles.Batch381.valid15241
  · exact MergedCutProfiles.Batch381.valid15242
  · exact MergedCutProfiles.Batch381.valid15243
  · exact MergedCutProfiles.Batch381.valid15244
  · exact MergedCutProfiles.Batch381.valid15245
  · exact MergedCutProfiles.Batch381.valid15246
theorem numericValid2449 : retention2449.NumericValid := by decide +kernel
def certificate2449 : RatCutBinCertificate := ⟨⟨retention2449,(1090065047647843647/500000000000000000),(136712609017002193/1000000000000000000),(13778560094102840813/1000000000000000000),(462528081660201628653/1000000000000000000),(418286398026459769/200000000000000000)⟩,(995900866633824653/1000000000000000000),(43709160858126447/125000000000000000),(282899533606873493/1000000000000000000),(154688746368771061/1000000000000000000)⟩
theorem valid2449 : certificate2449.Valid := by decide +kernel
theorem sound2449 : certificate2449.Sound := rat_cut_bin_certificate_sound certificate2449 profilesValid2449 numericValid2449 valid2449

def retention2450 : RatCutRetentionCertificate := ⟨(13/250),(53/1000),(992480763000000000/33373862222675650447),(964578272495270733/1000000000000000000),(27/10),(171035693671560061107/80000000000000000000),true,MergedCutProfiles.Batch381.profile15247,![MergedCutProfiles.Batch381.profile15247,MergedCutProfiles.Batch381.profile15248,MergedCutProfiles.Batch381.profile15249,MergedCutProfiles.Batch381.profile15250,MergedCutProfiles.Batch381.profile15251,MergedCutProfiles.Batch381.profile15252,MergedCutProfiles.Batch380.profile15222,MergedCutProfiles.Batch381.profile15253,MergedCutProfiles.Batch381.profile15254,MergedCutProfiles.Batch381.profile15255,MergedCutProfiles.Batch381.profile15256,MergedCutProfiles.Batch381.profile15257,MergedCutProfiles.Batch381.profile15258,MergedCutProfiles.Batch381.profile15259,MergedCutProfiles.Batch381.profile15260,MergedCutProfiles.Batch381.profile15261]⟩
theorem profilesValid2450 : retention2450.ProfilesValid := by
  change ∀ j : Fin 16, (retention2450.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch381.valid15247
  · exact MergedCutProfiles.Batch381.valid15248
  · exact MergedCutProfiles.Batch381.valid15249
  · exact MergedCutProfiles.Batch381.valid15250
  · exact MergedCutProfiles.Batch381.valid15251
  · exact MergedCutProfiles.Batch381.valid15252
  · exact MergedCutProfiles.Batch380.valid15222
  · exact MergedCutProfiles.Batch381.valid15253
  · exact MergedCutProfiles.Batch381.valid15254
  · exact MergedCutProfiles.Batch381.valid15255
  · exact MergedCutProfiles.Batch381.valid15256
  · exact MergedCutProfiles.Batch381.valid15257
  · exact MergedCutProfiles.Batch381.valid15258
  · exact MergedCutProfiles.Batch381.valid15259
  · exact MergedCutProfiles.Batch381.valid15260
  · exact MergedCutProfiles.Batch381.valid15261
theorem numericValid2450 : retention2450.NumericValid := by decide +kernel
def certificate2450 : RatCutBinCertificate := ⟨⟨retention2450,(1090065047647843647/500000000000000000),(136712609017002193/1000000000000000000),(13778560094102840813/1000000000000000000),(462528081660201628653/1000000000000000000),(2079534423608113783/1000000000000000000)⟩,(995900866633824653/1000000000000000000),(335557671213077789/1000000000000000000),(149008785346534361/500000000000000000),(176289803531606759/1000000000000000000)⟩
theorem valid2450 : certificate2450.Valid := by decide +kernel
theorem sound2450 : certificate2450.Sound := rat_cut_bin_certificate_sound certificate2450 profilesValid2450 numericValid2450 valid2450

def retention2451 : RatCutRetentionCertificate := ⟨(13/250),(53/1000),(1097780050378818019/33373862222675650447),(992480763/1000000000),(53/20),(3404785233801278251/1600000000000000000),true,MergedCutProfiles.Batch381.profile15262,![MergedCutProfiles.Batch381.profile15262,MergedCutProfiles.Batch381.profile15263,MergedCutProfiles.Batch381.profile15264,MergedCutProfiles.Batch381.profile15265,MergedCutProfiles.Batch381.profile15266,MergedCutProfiles.Batch381.profile15267,MergedCutProfiles.Batch381.profile15268,MergedCutProfiles.Batch381.profile15269,MergedCutProfiles.Batch381.profile15270,MergedCutProfiles.Batch381.profile15271,MergedCutProfiles.Batch381.profile15272,MergedCutProfiles.Batch381.profile15273,MergedCutProfiles.Batch381.profile15274,MergedCutProfiles.Batch381.profile15275,MergedCutProfiles.Batch381.profile15276,MergedCutProfiles.Batch381.profile15277]⟩
theorem profilesValid2451 : retention2451.ProfilesValid := by
  change ∀ j : Fin 16, (retention2451.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch381.valid15262
  · exact MergedCutProfiles.Batch381.valid15263
  · exact MergedCutProfiles.Batch381.valid15264
  · exact MergedCutProfiles.Batch381.valid15265
  · exact MergedCutProfiles.Batch381.valid15266
  · exact MergedCutProfiles.Batch381.valid15267
  · exact MergedCutProfiles.Batch381.valid15268
  · exact MergedCutProfiles.Batch381.valid15269
  · exact MergedCutProfiles.Batch381.valid15270
  · exact MergedCutProfiles.Batch381.valid15271
  · exact MergedCutProfiles.Batch381.valid15272
  · exact MergedCutProfiles.Batch381.valid15273
  · exact MergedCutProfiles.Batch381.valid15274
  · exact MergedCutProfiles.Batch381.valid15275
  · exact MergedCutProfiles.Batch381.valid15276
  · exact MergedCutProfiles.Batch381.valid15277
theorem numericValid2451 : retention2451.NumericValid := by decide +kernel
def certificate2451 : RatCutBinCertificate := ⟨⟨retention2451,(1090065047647843647/500000000000000000),(136712609017002193/1000000000000000000),(13778560094102840813/1000000000000000000),(462528081660201628653/1000000000000000000),(2070660786466838043/1000000000000000000)⟩,(995900866633824653/1000000000000000000),(41632718942296067/125000000000000000),(300751697678071927/1000000000000000000),(90151232801788273/500000000000000000)⟩
theorem valid2451 : certificate2451.Valid := by decide +kernel
theorem sound2451 : certificate2451.Sound := rat_cut_bin_certificate_sound certificate2451 profilesValid2451 numericValid2451 valid2451

def retention2452 : RatCutRetentionCertificate := ⟨(13/250),(53/1000),(2247264785967725495/33373862222675650447),(1097780050378818019/1000000000000000000),(49/20),(642510171682094362437/320000000000000000000),true,MergedCutProfiles.Batch381.profile15278,![MergedCutProfiles.Batch381.profile15278,MergedCutProfiles.Batch381.profile15279,MergedCutProfiles.Batch380.profile15237,MergedCutProfiles.Batch382.profile15280,MergedCutProfiles.Batch380.profile15227,MergedCutProfiles.Batch381.profile15244,MergedCutProfiles.Batch382.profile15281,MergedCutProfiles.Batch382.profile15282,MergedCutProfiles.Batch382.profile15283,MergedCutProfiles.Batch382.profile15284,MergedCutProfiles.Batch382.profile15285,MergedCutProfiles.Batch382.profile15286,MergedCutProfiles.Batch382.profile15287,MergedCutProfiles.Batch382.profile15288,MergedCutProfiles.Batch382.profile15289,MergedCutProfiles.Batch382.profile15290]⟩
theorem profilesValid2452 : retention2452.ProfilesValid := by
  change ∀ j : Fin 16, (retention2452.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch381.valid15278
  · exact MergedCutProfiles.Batch381.valid15279
  · exact MergedCutProfiles.Batch380.valid15237
  · exact MergedCutProfiles.Batch382.valid15280
  · exact MergedCutProfiles.Batch380.valid15227
  · exact MergedCutProfiles.Batch381.valid15244
  · exact MergedCutProfiles.Batch382.valid15281
  · exact MergedCutProfiles.Batch382.valid15282
  · exact MergedCutProfiles.Batch382.valid15283
  · exact MergedCutProfiles.Batch382.valid15284
  · exact MergedCutProfiles.Batch382.valid15285
  · exact MergedCutProfiles.Batch382.valid15286
  · exact MergedCutProfiles.Batch382.valid15287
  · exact MergedCutProfiles.Batch382.valid15288
  · exact MergedCutProfiles.Batch382.valid15289
  · exact MergedCutProfiles.Batch382.valid15290
theorem numericValid2452 : retention2452.NumericValid := by decide +kernel
def certificate2452 : RatCutBinCertificate := ⟨⟨retention2452,(1090065047647843647/500000000000000000),(136712609017002193/1000000000000000000),(13778560094102840813/1000000000000000000),(462528081660201628653/1000000000000000000),(1954841224876368299/1000000000000000000)⟩,(995900866633824653/1000000000000000000),(338977395018037017/1000000000000000000),(3678769054218789/12500000000000000),(180226946060860091/1000000000000000000)⟩
theorem valid2452 : certificate2452.Valid := by decide +kernel
theorem sound2452 : certificate2452.Sound := rat_cut_bin_certificate_sound certificate2452 profilesValid2452 numericValid2452 valid2452

def retention2453 : RatCutRetentionCertificate := ⟨(13/250),(53/1000),(9702780184956534960/33373862222675650447),(449452957193545099/200000000000000000),(3/2),(51324342419061510601302541322832499791/35956236575483607920000000000000000000),false,MergedCutProfiles.Batch382.profile15291,(fun _ => MergedCutProfiles.Batch382.profile15291)⟩
theorem profilesValid2453 : retention2453.ProfilesValid := by
  exact MergedCutProfiles.Batch382.valid15291
theorem numericValid2453 : retention2453.NumericValid := by decide +kernel
def certificate2453 : RatCutBinCertificate := ⟨⟨retention2453,(1090065047647843647/500000000000000000),(136712609017002193/1000000000000000000),(13778560094102840813/1000000000000000000),(462528081660201628653/1000000000000000000),(1394961278650797519/1000000000000000000)⟩,(995900866633824653/1000000000000000000),(381677104820435067/1000000000000000000),(10027868022003479/40000000000000000),(181876120589639717/1000000000000000000)⟩
theorem valid2453 : certificate2453.Valid := by decide +kernel
theorem sound2453 : certificate2453.Sound := rat_cut_bin_certificate_sound certificate2453 profilesValid2453 numericValid2453 valid2453

def retention2454 : RatCutRetentionCertificate := ⟨(13/250),(53/1000),(15957501052535783506/33373862222675650447),(121284752311956687/12500000000000000),(21/20),(157273201098667589378155042657468601/151605940389945858750000000000000000),false,MergedCutProfiles.Batch382.profile15292,(fun _ => MergedCutProfiles.Batch382.profile15292)⟩
theorem profilesValid2454 : retention2454.ProfilesValid := by
  exact MergedCutProfiles.Batch382.valid15292
theorem numericValid2454 : retention2454.NumericValid := by decide +kernel
def certificate2454 : RatCutBinCertificate := ⟨⟨retention2454,(1090065047647843647/500000000000000000),(136712609017002193/1000000000000000000),(13778560094102840813/1000000000000000000),(462528081660201628653/1000000000000000000),(1014667760739288681/1000000000000000000)⟩,(995900866633824653/1000000000000000000),(430549040719861033/1000000000000000000),(103314662255982373/500000000000000000),(181589597472822711/1000000000000000000)⟩
theorem valid2454 : certificate2454.Valid := by decide +kernel
theorem sound2454 : certificate2454.Sound := rat_cut_bin_certificate_sound certificate2454 profilesValid2454 numericValid2454 valid2454

def retention2455 : RatCutRetentionCertificate := ⟨(13/250),(53/1000),(16605439584847956987/33373862222675650447),(7978750526267891753/500000000000000000),1,(63229119554478566124525619743371410623/63830004210143134024000000000000000000),false,MergedCutProfiles.Batch382.profile15293,(fun _ => MergedCutProfiles.Batch382.profile15293)⟩
theorem profilesValid2455 : retention2455.ProfilesValid := by
  exact MergedCutProfiles.Batch382.valid15293
theorem numericValid2455 : retention2455.NumericValid := by decide +kernel
def certificate2455 : RatCutBinCertificate := ⟨⟨retention2455,(1090065047647843647/500000000000000000),(136712609017002193/1000000000000000000),(13778560094102840813/1000000000000000000),(462528081660201628653/1000000000000000000),(484477123135311217/500000000000000000)⟩,(995900866633824653/1000000000000000000),(439209715118384173/1000000000000000000),(199417680030209693/1000000000000000000),(18139220613037751/100000000000000000)⟩
theorem valid2455 : certificate2455.Valid := by decide +kernel
theorem sound2455 : certificate2455.Sound := rat_cut_bin_certificate_sound certificate2455 profilesValid2455 numericValid2455 valid2455

def retention2456 : RatCutRetentionCertificate := ⟨(13/250),(53/1000),(1/2),(16605439584847956987/1000000000000000000),1,(409515295399617902756558553925450337/415135989621198924675000000000000000),false,MergedCutProfiles.Batch382.profile15294,(fun _ => MergedCutProfiles.Batch382.profile15294)⟩
theorem profilesValid2456 : retention2456.ProfilesValid := by
  exact MergedCutProfiles.Batch382.valid15294
theorem numericValid2456 : retention2456.NumericValid := by decide +kernel
def certificate2456 : RatCutBinCertificate := ⟨⟨retention2456,(1090065047647843647/500000000000000000),(136712609017002193/1000000000000000000),(13778560094102840813/1000000000000000000),(462528081660201628653/1000000000000000000),(964828684683280583/1000000000000000000)⟩,(995900866633824653/1000000000000000000),(440379450879644961/1000000000000000000),(99228408878468891/500000000000000000),(180195259997753207/1000000000000000000)⟩
theorem valid2456 : certificate2456.Valid := by decide +kernel
theorem sound2456 : certificate2456.Sound := rat_cut_bin_certificate_sound certificate2456 profilesValid2456 numericValid2456 valid2456

def retention2457 : RatCutRetentionCertificate := ⟨(13/250),(53/1000),(14887769595053816859/33373862222675650447),(544967856026133419/100000000000000000),(21/20),(94010767628831575981317874279213534031/87194856964181347040000000000000000000),false,MergedCutProfiles.Batch382.profile15295,(fun _ => MergedCutProfiles.Batch382.profile15295)⟩
theorem profilesValid2457 : retention2457.ProfilesValid := by
  exact MergedCutProfiles.Batch382.valid15295
theorem numericValid2457 : retention2457.NumericValid := by decide +kernel
def certificate2457 : RatCutBinCertificate := ⟨⟨retention2457,(1224162177147843647/500000000000000000),(136712609017002193/1000000000000000000),(13778560094102840813/1000000000000000000),(462528081660201628653/1000000000000000000),(1052660194124996769/1000000000000000000)⟩,(39815850068132401/40000000000000000),(224263592119110231/1000000000000000000),(110078678861629151/250000000000000000),(74750877243696599/200000000000000000)⟩
theorem valid2457 : certificate2457.Valid := by decide +kernel
theorem sound2457 : certificate2457.Sound := rat_cut_bin_certificate_sound certificate2457 profilesValid2457 numericValid2457 valid2457

def retention2458 : RatCutRetentionCertificate := ⟨(13/250),(53/1000),(16445359692720654674/33373862222675650447),(14887769595053816859/1000000000000000000),1,(59476003533723569840168909058153997163/59551078380215267436000000000000000000),false,MergedCutProfiles.Batch382.profile15296,(fun _ => MergedCutProfiles.Batch382.profile15296)⟩
theorem profilesValid2458 : retention2458.ProfilesValid := by
  exact MergedCutProfiles.Batch382.valid15296
theorem numericValid2458 : retention2458.NumericValid := by decide +kernel
def certificate2458 : RatCutBinCertificate := ⟨⟨retention2458,(1224162177147843647/500000000000000000),(136712609017002193/1000000000000000000),(13778560094102840813/1000000000000000000),(462528081660201628653/1000000000000000000),(974446255147988191/1000000000000000000)⟩,(39815850068132401/40000000000000000),(6056602792819483/25000000000000000),(414168221954769367/1000000000000000000),(37698918661924787/100000000000000000)⟩
theorem valid2458 : certificate2458.Valid := by decide +kernel
theorem sound2458 : certificate2458.Sound := rat_cut_bin_certificate_sound certificate2458 profilesValid2458 numericValid2458 valid2458

def retention2459 : RatCutRetentionCertificate := ⟨(13/250),(53/1000),(16609813289647861221/33373862222675650447),(8222679846360327337/500000000000000000),1,(254595319025415167901919269722746209/256958745198760229281250000000000000),false,MergedCutProfiles.Batch382.profile15297,(fun _ => MergedCutProfiles.Batch382.profile15297)⟩
theorem profilesValid2459 : retention2459.ProfilesValid := by
  exact MergedCutProfiles.Batch382.valid15297
theorem numericValid2459 : retention2459.NumericValid := by decide +kernel
def certificate2459 : RatCutBinCertificate := ⟨⟨retention2459,(1224162177147843647/500000000000000000),(136712609017002193/1000000000000000000),(13778560094102840813/1000000000000000000),(462528081660201628653/1000000000000000000),(60406830841543871/62500000000000000)⟩,(39815850068132401/40000000000000000),(24425358143117881/100000000000000000),(51420116486511711/125000000000000000),(373733063520308923/1000000000000000000)⟩
theorem valid2459 : certificate2459.Valid := by decide +kernel
theorem sound2459 : certificate2459.Sound := rat_cut_bin_certificate_sound certificate2459 profilesValid2459 numericValid2459 valid2459

def certificates : List RatCutBinCertificate := [certificate2448,certificate2449,certificate2450,certificate2451,certificate2452,certificate2453,certificate2454,certificate2455,certificate2456,certificate2457,certificate2458,certificate2459]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound2448,List.forall_mem_cons.mpr ⟨sound2449,List.forall_mem_cons.mpr ⟨sound2450,List.forall_mem_cons.mpr ⟨sound2451,List.forall_mem_cons.mpr ⟨sound2452,List.forall_mem_cons.mpr ⟨sound2453,List.forall_mem_cons.mpr ⟨sound2454,List.forall_mem_cons.mpr ⟨sound2455,List.forall_mem_cons.mpr ⟨sound2456,List.forall_mem_cons.mpr ⟨sound2457,List.forall_mem_cons.mpr ⟨sound2458,List.forall_mem_cons.mpr ⟨sound2459,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch204
