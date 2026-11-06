import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch110
import Cycle12.MergedCutProfiles.Batch111

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch055

def retention660 : RatCutRetentionCertificate := ⟨(89/2000),(179/4000),(1/2),(6097139900577565353/500000000000000000),(21/20),(541091158832923646524034459892801394239/541967991162450253600000000000000000000),false,MergedCutProfiles.Batch110.profile4405,(fun _ => MergedCutProfiles.Batch110.profile4405)⟩
theorem profilesValid660 : retention660.ProfilesValid := by
  exact MergedCutProfiles.Batch110.valid4405
theorem numericValid660 : retention660.NumericValid := by decide +kernel
def certificate660 : RatCutBinCertificate := ⟨⟨retention660,(2489083162063887229/1000000000000000000),(11674148968388029/125000000000000000),(3044533470984429167/250000000000000000),(59831432486578824093/200000000000000000),(978338623027981719/1000000000000000000)⟩,(992441243461444659/1000000000000000000),(410382138515907867/1000000000000000000),(875403343812551/3906250000000000),(193121115115203719/1000000000000000000)⟩
theorem valid660 : certificate660.Valid := by decide +kernel
theorem sound660 : certificate660.Sound := rat_cut_bin_certificate_sound certificate660 profilesValid660 numericValid660 valid660

def retention661 : RatCutRetentionCertificate := ⟨(179/4000),(9/200),(825962236471870750/24225736566934492529),(817784392546406683/1000000000000000000),(61/20),(84618790373691785219/40000000000000000000),true,MergedCutProfiles.Batch110.profile4408,![MergedCutProfiles.Batch110.profile4408,MergedCutProfiles.Batch110.profile4409,MergedCutProfiles.Batch110.profile4410,MergedCutProfiles.Batch110.profile4411,MergedCutProfiles.Batch110.profile4412,MergedCutProfiles.Batch110.profile4413,MergedCutProfiles.Batch110.profile4414,MergedCutProfiles.Batch110.profile4415,MergedCutProfiles.Batch110.profile4416,MergedCutProfiles.Batch110.profile4417,MergedCutProfiles.Batch110.profile4418,MergedCutProfiles.Batch110.profile4419,MergedCutProfiles.Batch110.profile4420,MergedCutProfiles.Batch110.profile4421,MergedCutProfiles.Batch110.profile4422,MergedCutProfiles.Batch110.profile4423]⟩
theorem profilesValid661 : retention661.ProfilesValid := by
  change ∀ j : Fin 16, (retention661.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch110.valid4408
  · exact MergedCutProfiles.Batch110.valid4409
  · exact MergedCutProfiles.Batch110.valid4410
  · exact MergedCutProfiles.Batch110.valid4411
  · exact MergedCutProfiles.Batch110.valid4412
  · exact MergedCutProfiles.Batch110.valid4413
  · exact MergedCutProfiles.Batch110.valid4414
  · exact MergedCutProfiles.Batch110.valid4415
  · exact MergedCutProfiles.Batch110.valid4416
  · exact MergedCutProfiles.Batch110.valid4417
  · exact MergedCutProfiles.Batch110.valid4418
  · exact MergedCutProfiles.Batch110.valid4419
  · exact MergedCutProfiles.Batch110.valid4420
  · exact MergedCutProfiles.Batch110.valid4421
  · exact MergedCutProfiles.Batch110.valid4422
  · exact MergedCutProfiles.Batch110.valid4423
theorem numericValid661 : retention661.NumericValid := by decide +kernel
def certificate661 : RatCutBinCertificate := ⟨⟨retention661,(1056710354341272169/500000000000000000),(11819389720817643/125000000000000000),(12226730527229093307/1000000000000000000),(148306153012655465129/500000000000000000),(516403480926952797/250000000000000000)⟩,(993535855726060817/1000000000000000000),(387166991863584381/1000000000000000000),(245448592855465859/1000000000000000000),(64867968648466793/500000000000000000)⟩
theorem valid661 : certificate661.Valid := by decide +kernel
theorem sound661 : certificate661.Sound := rat_cut_bin_certificate_sound certificate661 profilesValid661 numericValid661 valid661

def retention662 : RatCutRetentionCertificate := ⟨(179/4000),(9/200),(880506844000000000/24225736566934492529),(3303848945887483/4000000000000000),(61/20),(270236373936348051403/128000000000000000000),true,MergedCutProfiles.Batch110.profile4424,![MergedCutProfiles.Batch110.profile4424,MergedCutProfiles.Batch110.profile4425,MergedCutProfiles.Batch110.profile4426,MergedCutProfiles.Batch110.profile4427,MergedCutProfiles.Batch110.profile4428,MergedCutProfiles.Batch110.profile4429,MergedCutProfiles.Batch110.profile4430,MergedCutProfiles.Batch110.profile4431,MergedCutProfiles.Batch110.profile4432,MergedCutProfiles.Batch110.profile4433,MergedCutProfiles.Batch110.profile4434,MergedCutProfiles.Batch110.profile4435,MergedCutProfiles.Batch110.profile4436,MergedCutProfiles.Batch110.profile4437,MergedCutProfiles.Batch110.profile4423,MergedCutProfiles.Batch110.profile4438]⟩
theorem profilesValid662 : retention662.ProfilesValid := by
  change ∀ j : Fin 16, (retention662.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch110.valid4424
  · exact MergedCutProfiles.Batch110.valid4425
  · exact MergedCutProfiles.Batch110.valid4426
  · exact MergedCutProfiles.Batch110.valid4427
  · exact MergedCutProfiles.Batch110.valid4428
  · exact MergedCutProfiles.Batch110.valid4429
  · exact MergedCutProfiles.Batch110.valid4430
  · exact MergedCutProfiles.Batch110.valid4431
  · exact MergedCutProfiles.Batch110.valid4432
  · exact MergedCutProfiles.Batch110.valid4433
  · exact MergedCutProfiles.Batch110.valid4434
  · exact MergedCutProfiles.Batch110.valid4435
  · exact MergedCutProfiles.Batch110.valid4436
  · exact MergedCutProfiles.Batch110.valid4437
  · exact MergedCutProfiles.Batch110.valid4423
  · exact MergedCutProfiles.Batch110.valid4438
theorem numericValid662 : retention662.NumericValid := by decide +kernel
def certificate662 : RatCutBinCertificate := ⟨⟨retention662,(1056710354341272169/500000000000000000),(11819389720817643/125000000000000000),(12226730527229093307/1000000000000000000),(148306153012655465129/500000000000000000),(2061365898823912013/1000000000000000000)⟩,(993535855726060817/1000000000000000000),(386304942453497783/1000000000000000000),(123133749969836261/500000000000000000),(130234185940101983/1000000000000000000)⟩
theorem valid662 : certificate662.Valid := by decide +kernel
theorem sound662 : certificate662.Sound := rat_cut_bin_certificate_sound certificate662 profilesValid662 numericValid662 valid662

def retention663 : RatCutRetentionCertificate := ⟨(179/4000),(9/200),(930714922000284865/24225736566934492529),(220126711/250000000),(57/20),(1675069919688561441/800000000000000000),true,MergedCutProfiles.Batch110.profile4439,![MergedCutProfiles.Batch110.profile4439,MergedCutProfiles.Batch111.profile4440,MergedCutProfiles.Batch111.profile4441,MergedCutProfiles.Batch111.profile4442,MergedCutProfiles.Batch111.profile4443,MergedCutProfiles.Batch111.profile4444,MergedCutProfiles.Batch111.profile4445,MergedCutProfiles.Batch110.profile4416,MergedCutProfiles.Batch111.profile4446,MergedCutProfiles.Batch111.profile4447,MergedCutProfiles.Batch111.profile4448,MergedCutProfiles.Batch111.profile4449,MergedCutProfiles.Batch111.profile4450,MergedCutProfiles.Batch111.profile4451,MergedCutProfiles.Batch111.profile4452,MergedCutProfiles.Batch111.profile4453]⟩
theorem profilesValid663 : retention663.ProfilesValid := by
  change ∀ j : Fin 16, (retention663.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch110.valid4439
  · exact MergedCutProfiles.Batch111.valid4440
  · exact MergedCutProfiles.Batch111.valid4441
  · exact MergedCutProfiles.Batch111.valid4442
  · exact MergedCutProfiles.Batch111.valid4443
  · exact MergedCutProfiles.Batch111.valid4444
  · exact MergedCutProfiles.Batch111.valid4445
  · exact MergedCutProfiles.Batch110.valid4416
  · exact MergedCutProfiles.Batch111.valid4446
  · exact MergedCutProfiles.Batch111.valid4447
  · exact MergedCutProfiles.Batch111.valid4448
  · exact MergedCutProfiles.Batch111.valid4449
  · exact MergedCutProfiles.Batch111.valid4450
  · exact MergedCutProfiles.Batch111.valid4451
  · exact MergedCutProfiles.Batch111.valid4452
  · exact MergedCutProfiles.Batch111.valid4453
theorem numericValid663 : retention663.NumericValid := by decide +kernel
def certificate663 : RatCutBinCertificate := ⟨⟨retention663,(1056710354341272169/500000000000000000),(11819389720817643/125000000000000000),(12226730527229093307/1000000000000000000),(148306153012655465129/500000000000000000),(409450167033008369/200000000000000000)⟩,(993535855726060817/1000000000000000000),(378614828413751291/1000000000000000000),(126829161458869661/500000000000000000),(35145814527342661/250000000000000000)⟩
theorem valid663 : certificate663.Valid := by decide +kernel
theorem sound663 : certificate663.Sound := rat_cut_bin_certificate_sound certificate663 profilesValid663 numericValid663 valid663

def retention664 : RatCutRetentionCertificate := ⟨(179/4000),(9/200),(1385707693675613919/24225736566934492529),(186142984400056973/200000000000000000),(11/4),(130185988105520185639/64000000000000000000),true,MergedCutProfiles.Batch111.profile4454,![MergedCutProfiles.Batch111.profile4454,MergedCutProfiles.Batch111.profile4441,MergedCutProfiles.Batch111.profile4455,MergedCutProfiles.Batch111.profile4456,MergedCutProfiles.Batch111.profile4457,MergedCutProfiles.Batch111.profile4458,MergedCutProfiles.Batch110.profile4434,MergedCutProfiles.Batch111.profile4459,MergedCutProfiles.Batch111.profile4460,MergedCutProfiles.Batch111.profile4461,MergedCutProfiles.Batch111.profile4462,MergedCutProfiles.Batch111.profile4463,MergedCutProfiles.Batch111.profile4464,MergedCutProfiles.Batch111.profile4465,MergedCutProfiles.Batch111.profile4466,MergedCutProfiles.Batch111.profile4467]⟩
theorem profilesValid664 : retention664.ProfilesValid := by
  change ∀ j : Fin 16, (retention664.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch111.valid4454
  · exact MergedCutProfiles.Batch111.valid4441
  · exact MergedCutProfiles.Batch111.valid4455
  · exact MergedCutProfiles.Batch111.valid4456
  · exact MergedCutProfiles.Batch111.valid4457
  · exact MergedCutProfiles.Batch111.valid4458
  · exact MergedCutProfiles.Batch110.valid4434
  · exact MergedCutProfiles.Batch111.valid4459
  · exact MergedCutProfiles.Batch111.valid4460
  · exact MergedCutProfiles.Batch111.valid4461
  · exact MergedCutProfiles.Batch111.valid4462
  · exact MergedCutProfiles.Batch111.valid4463
  · exact MergedCutProfiles.Batch111.valid4464
  · exact MergedCutProfiles.Batch111.valid4465
  · exact MergedCutProfiles.Batch111.valid4466
  · exact MergedCutProfiles.Batch111.valid4467
theorem numericValid664 : retention664.NumericValid := by decide +kernel
def certificate664 : RatCutBinCertificate := ⟨⟨retention664,(1056710354341272169/500000000000000000),(11819389720817643/125000000000000000),(12226730527229093307/1000000000000000000),(148306153012655465129/500000000000000000),(1989204227587878419/1000000000000000000)⟩,(993535855726060817/1000000000000000000),(380958571413107291/1000000000000000000),(1963979724267889/7812500000000000),(28139708912540071/200000000000000000)⟩
theorem valid664 : certificate664.Valid := by decide +kernel
theorem sound664 : certificate664.Sound := rat_cut_bin_certificate_sound certificate664 profilesValid664 numericValid664 valid664

def retention665 : RatCutRetentionCertificate := ⟨(179/4000),(9/200),(4619105227036063999/24225736566934492529),(1385707693675613919/1000000000000000000),(41/20),(3681839115770957080407713248308002038199/2217132309880982270400000000000000000000),false,MergedCutProfiles.Batch111.profile4468,(fun _ => MergedCutProfiles.Batch111.profile4468)⟩
theorem profilesValid665 : retention665.ProfilesValid := by
  exact MergedCutProfiles.Batch111.valid4468
theorem numericValid665 : retention665.NumericValid := by decide +kernel
def certificate665 : RatCutBinCertificate := ⟨⟨retention665,(1056710354341272169/500000000000000000),(11819389720817643/125000000000000000),(12226730527229093307/1000000000000000000),(148306153012655465129/500000000000000000),(813561037319481799/500000000000000000)⟩,(993535855726060817/1000000000000000000),(404455979142726423/1000000000000000000),(114712144482093447/500000000000000000),(141265585622509863/1000000000000000000)⟩
theorem valid665 : certificate665.Valid := by decide +kernel
theorem sound665 : certificate665.Sound := rat_cut_bin_certificate_sound certificate665 profilesValid665 numericValid665 valid665

def retention666 : RatCutRetentionCertificate := ⟨(179/4000),(9/200),(10549500083484970839/24225736566934492529),(4619105227036063999/1000000000000000000),(11/10),(2046463692066673637928606921333428431639/1847642090814425599600000000000000000000),false,MergedCutProfiles.Batch111.profile4469,(fun _ => MergedCutProfiles.Batch111.profile4469)⟩
theorem profilesValid666 : retention666.ProfilesValid := by
  exact MergedCutProfiles.Batch111.valid4469
theorem numericValid666 : retention666.NumericValid := by decide +kernel
def certificate666 : RatCutBinCertificate := ⟨⟨retention666,(1056710354341272169/500000000000000000),(11819389720817643/125000000000000000),(12226730527229093307/1000000000000000000),(148306153012655465129/500000000000000000),(544814332054907469/500000000000000000)⟩,(993535855726060817/1000000000000000000),(236471021613613167/500000000000000000),(172927135362183141/1000000000000000000),(7116810261458387/50000000000000000)⟩
theorem valid666 : certificate666.Valid := by decide +kernel
theorem sound666 : certificate666.Sound := rat_cut_bin_certificate_sound certificate666 profilesValid666 numericValid666 valid666

def retention667 : RatCutRetentionCertificate := ⟨(179/4000),(9/200),(11887440749450169357/24225736566934492529),(10549500083484970839/1000000000000000000),(21/20),(17122886688763854045383961979076125093319/16879200133575953342400000000000000000000),false,MergedCutProfiles.Batch111.profile4470,(fun _ => MergedCutProfiles.Batch111.profile4470)⟩
theorem profilesValid667 : retention667.ProfilesValid := by
  exact MergedCutProfiles.Batch111.valid4470
theorem numericValid667 : retention667.NumericValid := by decide +kernel
def certificate667 : RatCutBinCertificate := ⟨⟨retention667,(1056710354341272169/500000000000000000),(11819389720817643/125000000000000000),(12226730527229093307/1000000000000000000),(148306153012655465129/500000000000000000),(997275306469686243/1000000000000000000)⟩,(993535855726060817/1000000000000000000),(482250194293997313/1000000000000000000),(166048394385809819/1000000000000000000),(28854427114975769/200000000000000000)⟩
theorem valid667 : certificate667.Valid := by decide +kernel
theorem sound667 : certificate667.Sound := rat_cut_bin_certificate_sound certificate667 profilesValid667 numericValid667 valid667

def retention668 : RatCutRetentionCertificate := ⟨(179/4000),(9/200),(12006315156944671051/24225736566934492529),(11887440749450169357/1000000000000000000),(21/20),(6382485599817152794425438060499913476557/6339968399706756990400000000000000000000),false,MergedCutProfiles.Batch111.profile4471,(fun _ => MergedCutProfiles.Batch111.profile4471)⟩
theorem profilesValid668 : retention668.ProfilesValid := by
  exact MergedCutProfiles.Batch111.valid4471
theorem numericValid668 : retention668.NumericValid := by decide +kernel
def certificate668 : RatCutBinCertificate := ⟨⟨retention668,(1056710354341272169/500000000000000000),(11819389720817643/125000000000000000),(12226730527229093307/1000000000000000000),(148306153012655465129/500000000000000000),(24738612176476099/25000000000000000)⟩,(993535855726060817/1000000000000000000),(120742675926980419/250000000000000000),(82761736383595367/500000000000000000),(72032281323707107/500000000000000000)⟩
theorem valid668 : certificate668.Valid := by decide +kernel
theorem sound668 : certificate668.Sound := rat_cut_bin_certificate_sound certificate668 profilesValid668 numericValid668 valid668

def retention669 : RatCutRetentionCertificate := ⟨(179/4000),(9/200),(1/2),(12006315156944671051/1000000000000000000),(21/20),(19175116241700490804076316668783286785519/19210104251111473681600000000000000000000),false,MergedCutProfiles.Batch111.profile4472,(fun _ => MergedCutProfiles.Batch111.profile4472)⟩
theorem profilesValid669 : retention669.ProfilesValid := by
  exact MergedCutProfiles.Batch111.valid4472
theorem numericValid669 : retention669.NumericValid := by decide +kernel
def certificate669 : RatCutBinCertificate := ⟨⟨retention669,(1056710354341272169/500000000000000000),(11819389720817643/125000000000000000),(12226730527229093307/1000000000000000000),(148306153012655465129/500000000000000000),(981016941334121949/1000000000000000000)⟩,(993535855726060817/1000000000000000000),(121732251799643537/250000000000000000),(650635242521953/4000000000000000),(140533467018620457/1000000000000000000)⟩
theorem valid669 : certificate669.Valid := by decide +kernel
theorem sound669 : certificate669.Sound := rat_cut_bin_certificate_sound certificate669 profilesValid669 numericValid669 valid669

def retention670 : RatCutRetentionCertificate := ⟨(179/4000),(9/200),(10737257682664532819/24225736566934492529),(1888509322327770433/500000000000000000),(6/5),(104576473342961230678838072851904672591/94425466116388521650000000000000000000),false,MergedCutProfiles.Batch111.profile4473,(fun _ => MergedCutProfiles.Batch111.profile4473)⟩
theorem profilesValid670 : retention670.ProfilesValid := by
  exact MergedCutProfiles.Batch111.valid4473
theorem numericValid670 : retention670.NumericValid := by decide +kernel
def certificate670 : RatCutBinCertificate := ⟨⟨retention670,(1245821470341272169/500000000000000000),(11819389720817643/125000000000000000),(12226730527229093307/1000000000000000000),(148306153012655465129/500000000000000000),(542189179130269567/500000000000000000)⟩,(3876476994746011/3906250000000000),(184652009905456063/500000000000000000),(131407976608841487/500000000000000000),(196370826697679941/1000000000000000000)⟩
theorem valid670 : certificate670.Valid := by decide +kernel
theorem sound670 : certificate670.Sound := rat_cut_bin_certificate_sound certificate670 profilesValid670 numericValid670 valid670

def retention671 : RatCutRetentionCertificate := ⟨(179/4000),(9/200),(11979218526537807503/24225736566934492529),(10737257682664532819/1000000000000000000),(21/20),(17305348221199289522490009887784169621079/17179612292263252510400000000000000000000),false,MergedCutProfiles.Batch111.profile4474,(fun _ => MergedCutProfiles.Batch111.profile4474)⟩
theorem profilesValid671 : retention671.ProfilesValid := by
  exact MergedCutProfiles.Batch111.valid4474
theorem numericValid671 : retention671.NumericValid := by decide +kernel
def certificate671 : RatCutBinCertificate := ⟨⟨retention671,(1245821470341272169/500000000000000000),(11819389720817643/125000000000000000),(12226730527229093307/1000000000000000000),(148306153012655465129/500000000000000000),(98708581973669827/100000000000000000)⟩,(3876476994746011/3906250000000000),(202852314709777333/500000000000000000),(114147982312962753/500000000000000000),(98264462907988413/500000000000000000)⟩
theorem valid671 : certificate671.Valid := by decide +kernel
theorem sound671 : certificate671.Sound := rat_cut_bin_certificate_sound certificate671 profilesValid671 numericValid671 valid671

def certificates : List RatCutBinCertificate := [certificate660,certificate661,certificate662,certificate663,certificate664,certificate665,certificate666,certificate667,certificate668,certificate669,certificate670,certificate671]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound660,List.forall_mem_cons.mpr ⟨sound661,List.forall_mem_cons.mpr ⟨sound662,List.forall_mem_cons.mpr ⟨sound663,List.forall_mem_cons.mpr ⟨sound664,List.forall_mem_cons.mpr ⟨sound665,List.forall_mem_cons.mpr ⟨sound666,List.forall_mem_cons.mpr ⟨sound667,List.forall_mem_cons.mpr ⟨sound668,List.forall_mem_cons.mpr ⟨sound669,List.forall_mem_cons.mpr ⟨sound670,List.forall_mem_cons.mpr ⟨sound671,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch055
