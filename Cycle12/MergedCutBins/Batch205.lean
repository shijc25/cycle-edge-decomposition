import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch382
import Cycle12.MergedCutProfiles.Batch383
import Cycle12.MergedCutProfiles.Batch384

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch205

def retention2460 : RatCutRetentionCertificate := ⟨(13/250),(53/1000),(1/2),(16609813289647861221/1000000000000000000),1,(1024062022306002101635624102415814197/1038113330602991326312500000000000000),false,MergedCutProfiles.Batch382.profile15294,(fun _ => MergedCutProfiles.Batch382.profile15294)⟩
theorem profilesValid2460 : retention2460.ProfilesValid := by
  exact MergedCutProfiles.Batch382.valid15294
theorem numericValid2460 : retention2460.NumericValid := by decide +kernel
def certificate2460 : RatCutBinCertificate := ⟨⟨retention2460,(1224162177147843647/500000000000000000),(136712609017002193/1000000000000000000),(13778560094102840813/1000000000000000000),(462528081660201628653/1000000000000000000),(192434311396084873/200000000000000000)⟩,(39815850068132401/40000000000000000),(245354744382736567/1000000000000000000),(81962795792205931/200000000000000000),(57961318643909/156250000000000)⟩
theorem valid2460 : certificate2460.Valid := by decide +kernel
theorem sound2460 : certificate2460.Sound := rat_cut_bin_certificate_sound certificate2460 profilesValid2460 numericValid2460 valid2460

def retention2461 : RatCutRetentionCertificate := ⟨(53/1000),(27/500),(873085544057674753/31961439363656815796),(432220566365185521/500000000000000000),(59/20),(21528927574526722431/10000000000000000000),true,MergedCutProfiles.Batch382.profile15298,![MergedCutProfiles.Batch382.profile15298,MergedCutProfiles.Batch382.profile15299,MergedCutProfiles.Batch382.profile15300,MergedCutProfiles.Batch382.profile15301,MergedCutProfiles.Batch382.profile15302,MergedCutProfiles.Batch382.profile15303,MergedCutProfiles.Batch382.profile15304,MergedCutProfiles.Batch382.profile15305,MergedCutProfiles.Batch382.profile15306,MergedCutProfiles.Batch382.profile15307,MergedCutProfiles.Batch382.profile15308,MergedCutProfiles.Batch382.profile15309,MergedCutProfiles.Batch382.profile15310,MergedCutProfiles.Batch382.profile15311,MergedCutProfiles.Batch382.profile15312,MergedCutProfiles.Batch382.profile15313]⟩
theorem profilesValid2461 : retention2461.ProfilesValid := by
  change ∀ j : Fin 16, (retention2461.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch382.valid15298
  · exact MergedCutProfiles.Batch382.valid15299
  · exact MergedCutProfiles.Batch382.valid15300
  · exact MergedCutProfiles.Batch382.valid15301
  · exact MergedCutProfiles.Batch382.valid15302
  · exact MergedCutProfiles.Batch382.valid15303
  · exact MergedCutProfiles.Batch382.valid15304
  · exact MergedCutProfiles.Batch382.valid15305
  · exact MergedCutProfiles.Batch382.valid15306
  · exact MergedCutProfiles.Batch382.valid15307
  · exact MergedCutProfiles.Batch382.valid15308
  · exact MergedCutProfiles.Batch382.valid15309
  · exact MergedCutProfiles.Batch382.valid15310
  · exact MergedCutProfiles.Batch382.valid15311
  · exact MergedCutProfiles.Batch382.valid15312
  · exact MergedCutProfiles.Batch382.valid15313
theorem numericValid2461 : retention2461.NumericValid := by decide +kernel
def certificate2461 : RatCutBinCertificate := ⟨⟨retention2461,(2187464456303454291/1000000000000000000),(142705547327693923/1000000000000000000),(7007928973391192469/500000000000000000),(450599157594054054609/1000000000000000000),(2087181750580440143/1000000000000000000)⟩,(995806283356548963/1000000000000000000),(345196494574323629/1000000000000000000),(287631540072815079/1000000000000000000),(158513903793238029/1000000000000000000)⟩
theorem valid2461 : certificate2461.Valid := by decide +kernel
theorem sound2461 : certificate2461.Sound := rat_cut_bin_certificate_sound certificate2461 profilesValid2461 numericValid2461 valid2461

def retention2462 : RatCutRetentionCertificate := ⟨(53/1000),(27/500),(244392646000000000/7990359840914203949),(873085544057674753/1000000000000000000),(59/20),(2746664513912017846849/1280000000000000000000),true,MergedCutProfiles.Batch382.profile15314,![MergedCutProfiles.Batch382.profile15314,MergedCutProfiles.Batch382.profile15315,MergedCutProfiles.Batch382.profile15316,MergedCutProfiles.Batch382.profile15317,MergedCutProfiles.Batch382.profile15318,MergedCutProfiles.Batch382.profile15319,MergedCutProfiles.Batch383.profile15320,MergedCutProfiles.Batch382.profile15306,MergedCutProfiles.Batch383.profile15321,MergedCutProfiles.Batch383.profile15322,MergedCutProfiles.Batch383.profile15323,MergedCutProfiles.Batch383.profile15324,MergedCutProfiles.Batch383.profile15325,MergedCutProfiles.Batch383.profile15326,MergedCutProfiles.Batch383.profile15327,MergedCutProfiles.Batch383.profile15328]⟩
theorem profilesValid2462 : retention2462.ProfilesValid := by
  change ∀ j : Fin 16, (retention2462.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch382.valid15314
  · exact MergedCutProfiles.Batch382.valid15315
  · exact MergedCutProfiles.Batch382.valid15316
  · exact MergedCutProfiles.Batch382.valid15317
  · exact MergedCutProfiles.Batch382.valid15318
  · exact MergedCutProfiles.Batch382.valid15319
  · exact MergedCutProfiles.Batch383.valid15320
  · exact MergedCutProfiles.Batch382.valid15306
  · exact MergedCutProfiles.Batch383.valid15321
  · exact MergedCutProfiles.Batch383.valid15322
  · exact MergedCutProfiles.Batch383.valid15323
  · exact MergedCutProfiles.Batch383.valid15324
  · exact MergedCutProfiles.Batch383.valid15325
  · exact MergedCutProfiles.Batch383.valid15326
  · exact MergedCutProfiles.Batch383.valid15327
  · exact MergedCutProfiles.Batch383.valid15328
theorem numericValid2462 : retention2462.NumericValid := by decide +kernel
def certificate2462 : RatCutBinCertificate := ⟨⟨retention2462,(2187464456303454291/1000000000000000000),(142705547327693923/1000000000000000000),(7007928973391192469/500000000000000000),(450599157594054054609/1000000000000000000),(2080120725411205891/1000000000000000000)⟩,(995806283356548963/1000000000000000000),(344864415431079683/1000000000000000000),(71996212612020963/250000000000000000),(39657269761555129/250000000000000000)⟩
theorem valid2462 : certificate2462.Valid := by decide +kernel
theorem sound2462 : certificate2462.Sound := rat_cut_bin_certificate_sound certificate2462 profilesValid2462 numericValid2462 valid2462

def retention2463 : RatCutRetentionCertificate := ⟨(53/1000),(27/500),(983814644490576539/31961439363656815796),(122196323/125000000),(53/20),(4260012706456085453/2000000000000000000),true,MergedCutProfiles.Batch382.profile15314,![MergedCutProfiles.Batch382.profile15314,MergedCutProfiles.Batch383.profile15329,MergedCutProfiles.Batch382.profile15316,MergedCutProfiles.Batch382.profile15317,MergedCutProfiles.Batch382.profile15318,MergedCutProfiles.Batch383.profile15330,MergedCutProfiles.Batch383.profile15331,MergedCutProfiles.Batch383.profile15332,MergedCutProfiles.Batch383.profile15333,MergedCutProfiles.Batch383.profile15334,MergedCutProfiles.Batch383.profile15335,MergedCutProfiles.Batch383.profile15336,MergedCutProfiles.Batch383.profile15337,MergedCutProfiles.Batch383.profile15338,MergedCutProfiles.Batch383.profile15339,MergedCutProfiles.Batch383.profile15340]⟩
theorem profilesValid2463 : retention2463.ProfilesValid := by
  change ∀ j : Fin 16, (retention2463.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch382.valid15314
  · exact MergedCutProfiles.Batch383.valid15329
  · exact MergedCutProfiles.Batch382.valid15316
  · exact MergedCutProfiles.Batch382.valid15317
  · exact MergedCutProfiles.Batch382.valid15318
  · exact MergedCutProfiles.Batch383.valid15330
  · exact MergedCutProfiles.Batch383.valid15331
  · exact MergedCutProfiles.Batch383.valid15332
  · exact MergedCutProfiles.Batch383.valid15333
  · exact MergedCutProfiles.Batch383.valid15334
  · exact MergedCutProfiles.Batch383.valid15335
  · exact MergedCutProfiles.Batch383.valid15336
  · exact MergedCutProfiles.Batch383.valid15337
  · exact MergedCutProfiles.Batch383.valid15338
  · exact MergedCutProfiles.Batch383.valid15339
  · exact MergedCutProfiles.Batch383.valid15340
theorem numericValid2463 : retention2463.NumericValid := by decide +kernel
def certificate2463 : RatCutBinCertificate := ⟨⟨retention2463,(2187464456303454291/1000000000000000000),(142705547327693923/1000000000000000000),(7007928973391192469/500000000000000000),(450599157594054054609/1000000000000000000),(1035488968056916399/500000000000000000)⟩,(995806283356548963/1000000000000000000),(330242349427161579/1000000000000000000),(37982829110845687/125000000000000000),(181531653413473267/1000000000000000000)⟩
theorem valid2463 : certificate2463.Valid := by decide +kernel
theorem sound2463 : certificate2463.Sound := rat_cut_bin_certificate_sound certificate2463 profilesValid2463 numericValid2463 valid2463

def retention2464 : RatCutRetentionCertificate := ⟨(53/1000),(27/500),(149191295654729441/4565919909093830828),(983814644490576539/1000000000000000000),(53/20),(85055886723246811931/40000000000000000000),true,MergedCutProfiles.Batch383.profile15341,![MergedCutProfiles.Batch383.profile15341,MergedCutProfiles.Batch383.profile15342,MergedCutProfiles.Batch383.profile15343,MergedCutProfiles.Batch383.profile15344,MergedCutProfiles.Batch383.profile15345,MergedCutProfiles.Batch383.profile15346,MergedCutProfiles.Batch383.profile15347,MergedCutProfiles.Batch383.profile15348,MergedCutProfiles.Batch383.profile15349,MergedCutProfiles.Batch383.profile15350,MergedCutProfiles.Batch383.profile15351,MergedCutProfiles.Batch383.profile15352,MergedCutProfiles.Batch383.profile15353,MergedCutProfiles.Batch383.profile15327,MergedCutProfiles.Batch383.profile15328,MergedCutProfiles.Batch383.profile15354]⟩
theorem profilesValid2464 : retention2464.ProfilesValid := by
  change ∀ j : Fin 16, (retention2464.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch383.valid15341
  · exact MergedCutProfiles.Batch383.valid15342
  · exact MergedCutProfiles.Batch383.valid15343
  · exact MergedCutProfiles.Batch383.valid15344
  · exact MergedCutProfiles.Batch383.valid15345
  · exact MergedCutProfiles.Batch383.valid15346
  · exact MergedCutProfiles.Batch383.valid15347
  · exact MergedCutProfiles.Batch383.valid15348
  · exact MergedCutProfiles.Batch383.valid15349
  · exact MergedCutProfiles.Batch383.valid15350
  · exact MergedCutProfiles.Batch383.valid15351
  · exact MergedCutProfiles.Batch383.valid15352
  · exact MergedCutProfiles.Batch383.valid15353
  · exact MergedCutProfiles.Batch383.valid15327
  · exact MergedCutProfiles.Batch383.valid15328
  · exact MergedCutProfiles.Batch383.valid15354
theorem numericValid2464 : retention2464.NumericValid := by decide +kernel
def certificate2464 : RatCutBinCertificate := ⟨⟨retention2464,(2187464456303454291/1000000000000000000),(142705547327693923/1000000000000000000),(7007928973391192469/500000000000000000),(450599157594054054609/1000000000000000000),(516842199190497583/250000000000000000)⟩,(995806283356548963/1000000000000000000),(164980583030596169/500000000000000000),(19010887797667689/62500000000000000),(181741985222647063/1000000000000000000)⟩
theorem valid2464 : certificate2464.Valid := by decide +kernel
theorem sound2464 : certificate2464.Sound := rat_cut_bin_certificate_sound certificate2464 profilesValid2464 numericValid2464 valid2464

def retention2465 : RatCutRetentionCertificate := ⟨(53/1000),(27/500),(429388316657802085/7990359840914203949),(1044339069583106087/1000000000000000000),(5/2),(524116370304912340183/256000000000000000000),true,MergedCutProfiles.Batch383.profile15355,![MergedCutProfiles.Batch383.profile15355,MergedCutProfiles.Batch383.profile15356,MergedCutProfiles.Batch383.profile15357,MergedCutProfiles.Batch383.profile15331,MergedCutProfiles.Batch383.profile15358,MergedCutProfiles.Batch383.profile15359,MergedCutProfiles.Batch384.profile15360,MergedCutProfiles.Batch383.profile15326,MergedCutProfiles.Batch384.profile15361,MergedCutProfiles.Batch384.profile15362,MergedCutProfiles.Batch384.profile15363,MergedCutProfiles.Batch384.profile15364,MergedCutProfiles.Batch384.profile15365,MergedCutProfiles.Batch384.profile15366,MergedCutProfiles.Batch384.profile15367,MergedCutProfiles.Batch384.profile15368]⟩
theorem profilesValid2465 : retention2465.ProfilesValid := by
  change ∀ j : Fin 16, (retention2465.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch383.valid15355
  · exact MergedCutProfiles.Batch383.valid15356
  · exact MergedCutProfiles.Batch383.valid15357
  · exact MergedCutProfiles.Batch383.valid15331
  · exact MergedCutProfiles.Batch383.valid15358
  · exact MergedCutProfiles.Batch383.valid15359
  · exact MergedCutProfiles.Batch384.valid15360
  · exact MergedCutProfiles.Batch383.valid15326
  · exact MergedCutProfiles.Batch384.valid15361
  · exact MergedCutProfiles.Batch384.valid15362
  · exact MergedCutProfiles.Batch384.valid15363
  · exact MergedCutProfiles.Batch384.valid15364
  · exact MergedCutProfiles.Batch384.valid15365
  · exact MergedCutProfiles.Batch384.valid15366
  · exact MergedCutProfiles.Batch384.valid15367
  · exact MergedCutProfiles.Batch384.valid15368
theorem numericValid2465 : retention2465.NumericValid := by decide +kernel
def certificate2465 : RatCutBinCertificate := ⟨⟨retention2465,(2187464456303454291/1000000000000000000),(142705547327693923/1000000000000000000),(7007928973391192469/500000000000000000),(450599157594054054609/1000000000000000000),(995821219217892903/500000000000000000)⟩,(995806283356548963/1000000000000000000),(334428733552096449/1000000000000000000),(299251950012805733/1000000000000000000),(18176238234581647/100000000000000000)⟩
theorem valid2465 : certificate2465.Valid := by decide +kernel
theorem sound2465 : certificate2465.Sound := rat_cut_bin_certificate_sound certificate2465 profilesValid2465 numericValid2465 valid2465

def retention2466 : RatCutRetentionCertificate := ⟨(53/1000),(27/500),(6985924988896239685/31961439363656815796),(85877663331560417/50000000000000000),(9/5),(548537062527085153721727644217731611/343510653326241668000000000000000000),false,MergedCutProfiles.Batch384.profile15369,(fun _ => MergedCutProfiles.Batch384.profile15369)⟩
theorem profilesValid2466 : retention2466.ProfilesValid := by
  exact MergedCutProfiles.Batch384.valid15369
theorem numericValid2466 : retention2466.NumericValid := by decide +kernel
def certificate2466 : RatCutBinCertificate := ⟨⟨retention2466,(2187464456303454291/1000000000000000000),(142705547327693923/1000000000000000000),(7007928973391192469/500000000000000000),(450599157594054054609/1000000000000000000),(389190515796372669/250000000000000000)⟩,(995806283356548963/1000000000000000000),(18100242892604657/50000000000000000),(270158732315493893/1000000000000000000),(181693686450701599/1000000000000000000)⟩
theorem valid2466 : certificate2466.Valid := by decide +kernel
theorem sound2466 : certificate2466.Sound := rat_cut_bin_certificate_sound certificate2466 profilesValid2466 numericValid2466 valid2466

def retention2467 : RatCutRetentionCertificate := ⟨(53/1000),(27/500),(7294164986079787245/15980719681828407898),(1397184997779247937/200000000000000000),1,(53662999196297878337/51200000000000000000),true,MergedCutProfiles.Batch384.profile15370,![MergedCutProfiles.Batch384.profile15370,MergedCutProfiles.Batch384.profile15371,MergedCutProfiles.Batch384.profile15372,MergedCutProfiles.Batch384.profile15373,MergedCutProfiles.Batch384.profile15374,MergedCutProfiles.Batch384.profile15375,MergedCutProfiles.Batch384.profile15376,MergedCutProfiles.Batch384.profile15377,MergedCutProfiles.Batch384.profile15378,MergedCutProfiles.Batch384.profile15379,MergedCutProfiles.Batch384.profile15380,MergedCutProfiles.Batch384.profile15381,MergedCutProfiles.Batch384.profile15382,MergedCutProfiles.Batch384.profile15383,MergedCutProfiles.Batch384.profile15384,MergedCutProfiles.Batch384.profile15385]⟩
theorem profilesValid2467 : retention2467.ProfilesValid := by
  change ∀ j : Fin 16, (retention2467.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch384.valid15370
  · exact MergedCutProfiles.Batch384.valid15371
  · exact MergedCutProfiles.Batch384.valid15372
  · exact MergedCutProfiles.Batch384.valid15373
  · exact MergedCutProfiles.Batch384.valid15374
  · exact MergedCutProfiles.Batch384.valid15375
  · exact MergedCutProfiles.Batch384.valid15376
  · exact MergedCutProfiles.Batch384.valid15377
  · exact MergedCutProfiles.Batch384.valid15378
  · exact MergedCutProfiles.Batch384.valid15379
  · exact MergedCutProfiles.Batch384.valid15380
  · exact MergedCutProfiles.Batch384.valid15381
  · exact MergedCutProfiles.Batch384.valid15382
  · exact MergedCutProfiles.Batch384.valid15383
  · exact MergedCutProfiles.Batch384.valid15384
  · exact MergedCutProfiles.Batch384.valid15385
theorem numericValid2467 : retention2467.NumericValid := by decide +kernel
def certificate2467 : RatCutBinCertificate := ⟨⟨retention2467,(2187464456303454291/1000000000000000000),(142705547327693923/1000000000000000000),(7007928973391192469/500000000000000000),(450599157594054054609/1000000000000000000),(1025832291796652443/1000000000000000000)⟩,(995806283356548963/1000000000000000000),(54057893509719513/125000000000000000),(102510298455464239/500000000000000000),(182560536715581013/1000000000000000000)⟩
theorem valid2467 : certificate2467.Valid := by decide +kernel
theorem sound2467 : certificate2467.Sound := rat_cut_bin_certificate_sound certificate2467 profilesValid2467 numericValid2467 valid2467

def retention2468 : RatCutRetentionCertificate := ⟨(53/1000),(27/500),(15797070934268098317/31961439363656815796),(1458832997215957449/100000000000000000),1,(4840885021198092166003126328872481097/4862776657386524830000000000000000000),false,MergedCutProfiles.Batch384.profile15386,(fun _ => MergedCutProfiles.Batch384.profile15386)⟩
theorem profilesValid2468 : retention2468.ProfilesValid := by
  exact MergedCutProfiles.Batch384.valid15386
theorem numericValid2468 : retention2468.NumericValid := by decide +kernel
def certificate2468 : RatCutBinCertificate := ⟨⟨retention2468,(2187464456303454291/1000000000000000000),(142705547327693923/1000000000000000000),(7007928973391192469/500000000000000000),(450599157594054054609/1000000000000000000),(486612742543093069/500000000000000000)⟩,(995806283356548963/1000000000000000000),(434905162627627881/1000000000000000000),(101490238405463643/500000000000000000),(184384388579874229/1000000000000000000)⟩
theorem valid2468 : certificate2468.Valid := by decide +kernel
theorem sound2468 : certificate2468.Sound := rat_cut_bin_certificate_sound certificate2468 profilesValid2468 numericValid2468 valid2468

def retention2469 : RatCutRetentionCertificate := ⟨(53/1000),(27/500),(15955041643610779301/31961439363656815796),(15797070934268098317/1000000000000000000),1,(62382701467797727355661536258636021507/63188283737072393268000000000000000000),false,MergedCutProfiles.Batch384.profile15387,(fun _ => MergedCutProfiles.Batch384.profile15387)⟩
theorem profilesValid2469 : retention2469.ProfilesValid := by
  exact MergedCutProfiles.Batch384.valid15387
theorem numericValid2469 : retention2469.NumericValid := by decide +kernel
def certificate2469 : RatCutBinCertificate := ⟨⟨retention2469,(2187464456303454291/1000000000000000000),(142705547327693923/1000000000000000000),(7007928973391192469/500000000000000000),(450599157594054054609/1000000000000000000),(48248924179131453/50000000000000000)⟩,(995806283356548963/1000000000000000000),(109284369218753001/250000000000000000),(20112754165449979/100000000000000000),(182115766674140883/1000000000000000000)⟩
theorem valid2469 : certificate2469.Valid := by decide +kernel
theorem sound2469 : certificate2469.Sound := rat_cut_bin_certificate_sound certificate2469 profilesValid2469 numericValid2469 valid2469

def retention2470 : RatCutRetentionCertificate := ⟨(53/1000),(27/500),(1/2),(15955041643610779301/1000000000000000000),1,(3145855010526063491532526388476935669/3191008328722155860200000000000000000),false,MergedCutProfiles.Batch384.profile15388,(fun _ => MergedCutProfiles.Batch384.profile15388)⟩
theorem profilesValid2470 : retention2470.ProfilesValid := by
  exact MergedCutProfiles.Batch384.valid15388
theorem numericValid2470 : retention2470.NumericValid := by decide +kernel
def certificate2470 : RatCutBinCertificate := ⟨⟨retention2470,(2187464456303454291/1000000000000000000),(142705547327693923/1000000000000000000),(7007928973391192469/500000000000000000),(450599157594054054609/1000000000000000000),(481788616937061483/500000000000000000)⟩,(995806283356548963/1000000000000000000),(437595518317526543/1000000000000000000),(200748754955938587/1000000000000000000),(181627646594101929/1000000000000000000)⟩
theorem valid2470 : certificate2470.Valid := by decide +kernel
theorem sound2470 : certificate2470.Sound := rat_cut_bin_certificate_sound certificate2470 profilesValid2470 numericValid2470 valid2470

def retention2471 : RatCutRetentionCertificate := ⟨(53/1000),(27/500),(3572077395257037269/7990359840914203949),(2694363738654067187/500000000000000000),(21/20),(2318842967694266065059737809204422194511/2155490990923253749600000000000000000000),false,MergedCutProfiles.Batch384.profile15389,(fun _ => MergedCutProfiles.Batch384.profile15389)⟩
theorem profilesValid2471 : retention2471.ProfilesValid := by
  exact MergedCutProfiles.Batch384.valid15389
theorem numericValid2471 : retention2471.NumericValid := by decide +kernel
def certificate2471 : RatCutBinCertificate := ⟨⟨retention2471,(2458777814303454291/1000000000000000000),(142705547327693923/1000000000000000000),(7007928973391192469/500000000000000000),(450599157594054054609/1000000000000000000),(1049496325774800553/1000000000000000000)⟩,(248821436070388231/250000000000000000),(113170292725457479/500000000000000000),(437227575533307529/1000000000000000000),(369515961268548133/1000000000000000000)⟩
theorem valid2471 : certificate2471.Valid := by decide +kernel
theorem sound2471 : certificate2471.Sound := rat_cut_bin_certificate_sound certificate2471 profilesValid2471 numericValid2471 valid2471

def certificates : List RatCutBinCertificate := [certificate2460,certificate2461,certificate2462,certificate2463,certificate2464,certificate2465,certificate2466,certificate2467,certificate2468,certificate2469,certificate2470,certificate2471]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound2460,List.forall_mem_cons.mpr ⟨sound2461,List.forall_mem_cons.mpr ⟨sound2462,List.forall_mem_cons.mpr ⟨sound2463,List.forall_mem_cons.mpr ⟨sound2464,List.forall_mem_cons.mpr ⟨sound2465,List.forall_mem_cons.mpr ⟨sound2466,List.forall_mem_cons.mpr ⟨sound2467,List.forall_mem_cons.mpr ⟨sound2468,List.forall_mem_cons.mpr ⟨sound2469,List.forall_mem_cons.mpr ⟨sound2470,List.forall_mem_cons.mpr ⟨sound2471,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch205
