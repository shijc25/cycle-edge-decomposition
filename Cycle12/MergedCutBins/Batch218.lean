import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch410
import Cycle12.MergedCutProfiles.Batch411
import Cycle12.MergedCutProfiles.Batch412

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch218

def retention2616 : RatCutRetentionCertificate := ⟨(123/2000),(31/500),(993835887811454201/23102356905764287544),(973755931/1000000000),(51/20),(8301541186827897627/4000000000000000000),true,MergedCutProfiles.Batch410.profile16413,![MergedCutProfiles.Batch410.profile16413,MergedCutProfiles.Batch410.profile16414,MergedCutProfiles.Batch410.profile16415,MergedCutProfiles.Batch410.profile16416,MergedCutProfiles.Batch410.profile16417,MergedCutProfiles.Batch410.profile16418,MergedCutProfiles.Batch410.profile16419,MergedCutProfiles.Batch410.profile16420,MergedCutProfiles.Batch410.profile16421,MergedCutProfiles.Batch410.profile16422,MergedCutProfiles.Batch410.profile16423,MergedCutProfiles.Batch410.profile16424,MergedCutProfiles.Batch410.profile16425,MergedCutProfiles.Batch410.profile16426,MergedCutProfiles.Batch410.profile16427,MergedCutProfiles.Batch410.profile16428]⟩
theorem profilesValid2616 : retention2616.ProfilesValid := by
  change ∀ j : Fin 16, (retention2616.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch410.valid16413
  · exact MergedCutProfiles.Batch410.valid16414
  · exact MergedCutProfiles.Batch410.valid16415
  · exact MergedCutProfiles.Batch410.valid16416
  · exact MergedCutProfiles.Batch410.valid16417
  · exact MergedCutProfiles.Batch410.valid16418
  · exact MergedCutProfiles.Batch410.valid16419
  · exact MergedCutProfiles.Batch410.valid16420
  · exact MergedCutProfiles.Batch410.valid16421
  · exact MergedCutProfiles.Batch410.valid16422
  · exact MergedCutProfiles.Batch410.valid16423
  · exact MergedCutProfiles.Batch410.valid16424
  · exact MergedCutProfiles.Batch410.valid16425
  · exact MergedCutProfiles.Batch410.valid16426
  · exact MergedCutProfiles.Batch410.valid16427
  · exact MergedCutProfiles.Batch410.valid16428
theorem numericValid2616 : retention2616.NumericValid := by decide +kernel
def certificate2616 : RatCutBinCertificate := ⟨⟨retention2616,(1147499597416809633/500000000000000000),(24651154762240763/125000000000000000),(8155537656678971133/500000000000000000),(94498107574152091661/250000000000000000),(2004613760670379049/1000000000000000000)⟩,(62193564122656627/62500000000000000),(58262238401061977/200000000000000000),(682358017410599/1953125000000000),(207378940114377463/1000000000000000000)⟩
theorem valid2616 : certificate2616.Valid := by decide +kernel
theorem sound2616 : certificate2616.Sound := rat_cut_bin_certificate_sound certificate2616 profilesValid2616 numericValid2616 valid2616

def retention2617 : RatCutRetentionCertificate := ⟨(123/2000),(31/500),(294251061498140201/5775589226441071886),(993835887811454201/1000000000000000000),(5/2),(32779654822915666007/16000000000000000000),true,MergedCutProfiles.Batch410.profile16429,![MergedCutProfiles.Batch410.profile16429,MergedCutProfiles.Batch410.profile16430,MergedCutProfiles.Batch410.profile16431,MergedCutProfiles.Batch410.profile16432,MergedCutProfiles.Batch410.profile16433,MergedCutProfiles.Batch410.profile16434,MergedCutProfiles.Batch410.profile16435,MergedCutProfiles.Batch410.profile16436,MergedCutProfiles.Batch410.profile16437,MergedCutProfiles.Batch410.profile16438,MergedCutProfiles.Batch410.profile16439,MergedCutProfiles.Batch411.profile16440,MergedCutProfiles.Batch411.profile16441,MergedCutProfiles.Batch411.profile16442,MergedCutProfiles.Batch411.profile16443,MergedCutProfiles.Batch411.profile16444]⟩
theorem profilesValid2617 : retention2617.ProfilesValid := by
  change ∀ j : Fin 16, (retention2617.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch410.valid16429
  · exact MergedCutProfiles.Batch410.valid16430
  · exact MergedCutProfiles.Batch410.valid16431
  · exact MergedCutProfiles.Batch410.valid16432
  · exact MergedCutProfiles.Batch410.valid16433
  · exact MergedCutProfiles.Batch410.valid16434
  · exact MergedCutProfiles.Batch410.valid16435
  · exact MergedCutProfiles.Batch410.valid16436
  · exact MergedCutProfiles.Batch410.valid16437
  · exact MergedCutProfiles.Batch410.valid16438
  · exact MergedCutProfiles.Batch410.valid16439
  · exact MergedCutProfiles.Batch411.valid16440
  · exact MergedCutProfiles.Batch411.valid16441
  · exact MergedCutProfiles.Batch411.valid16442
  · exact MergedCutProfiles.Batch411.valid16443
  · exact MergedCutProfiles.Batch411.valid16444
theorem numericValid2617 : retention2617.NumericValid := by decide +kernel
def certificate2617 : RatCutBinCertificate := ⟨⟨retention2617,(1147499597416809633/500000000000000000),(24651154762240763/125000000000000000),(8155537656678971133/500000000000000000),(94498107574152091661/250000000000000000),(1979344576443270753/1000000000000000000)⟩,(62193564122656627/62500000000000000),(36590638942718077/125000000000000000),(347627922360897211/1000000000000000000),(103747463807652683/500000000000000000)⟩
theorem valid2617 : certificate2617.Valid := by decide +kernel
theorem sound2617 : certificate2617.Sound := rat_cut_bin_certificate_sound certificate2617 profilesValid2617 numericValid2617 valid2617

def retention2618 : RatCutRetentionCertificate := ⟨(123/2000),(31/500),(2635174055021901493/23102356905764287544),(294251061498140201/250000000000000000),(11/5),(596189199051245179501/320000000000000000000),true,MergedCutProfiles.Batch411.profile16445,![MergedCutProfiles.Batch411.profile16445,MergedCutProfiles.Batch411.profile16446,MergedCutProfiles.Batch411.profile16447,MergedCutProfiles.Batch411.profile16448,MergedCutProfiles.Batch411.profile16449,MergedCutProfiles.Batch411.profile16450,MergedCutProfiles.Batch411.profile16451,MergedCutProfiles.Batch411.profile16452,MergedCutProfiles.Batch411.profile16453,MergedCutProfiles.Batch411.profile16454,MergedCutProfiles.Batch411.profile16455,MergedCutProfiles.Batch411.profile16456,MergedCutProfiles.Batch411.profile16457,MergedCutProfiles.Batch411.profile16458,MergedCutProfiles.Batch411.profile16459,MergedCutProfiles.Batch411.profile16460]⟩
theorem profilesValid2618 : retention2618.ProfilesValid := by
  change ∀ j : Fin 16, (retention2618.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch411.valid16445
  · exact MergedCutProfiles.Batch411.valid16446
  · exact MergedCutProfiles.Batch411.valid16447
  · exact MergedCutProfiles.Batch411.valid16448
  · exact MergedCutProfiles.Batch411.valid16449
  · exact MergedCutProfiles.Batch411.valid16450
  · exact MergedCutProfiles.Batch411.valid16451
  · exact MergedCutProfiles.Batch411.valid16452
  · exact MergedCutProfiles.Batch411.valid16453
  · exact MergedCutProfiles.Batch411.valid16454
  · exact MergedCutProfiles.Batch411.valid16455
  · exact MergedCutProfiles.Batch411.valid16456
  · exact MergedCutProfiles.Batch411.valid16457
  · exact MergedCutProfiles.Batch411.valid16458
  · exact MergedCutProfiles.Batch411.valid16459
  · exact MergedCutProfiles.Batch411.valid16460
theorem numericValid2618 : retention2618.NumericValid := by decide +kernel
def certificate2618 : RatCutBinCertificate := ⟨⟨retention2618,(1147499597416809633/500000000000000000),(24651154762240763/125000000000000000),(8155537656678971133/500000000000000000),(94498107574152091661/250000000000000000),(1802033977941937591/1000000000000000000)⟩,(62193564122656627/62500000000000000),(12096805453716347/40000000000000000),(335882551772822093/1000000000000000000),(207789476649166551/1000000000000000000)⟩
theorem valid2618 : certificate2618.Valid := by decide +kernel
theorem sound2618 : certificate2618.Sound := rat_cut_bin_certificate_sound certificate2618 profilesValid2618 numericValid2618 valid2618

def retention2619 : RatCutRetentionCertificate := ⟨(123/2000),(31/500),(8111936519043882443/23102356905764287544),(2635174055021901493/1000000000000000000),(13/10),(1645980386217018056897/1280000000000000000000),true,MergedCutProfiles.Batch411.profile16461,![MergedCutProfiles.Batch411.profile16461,MergedCutProfiles.Batch411.profile16462,MergedCutProfiles.Batch411.profile16463,MergedCutProfiles.Batch411.profile16464,MergedCutProfiles.Batch411.profile16465,MergedCutProfiles.Batch411.profile16466,MergedCutProfiles.Batch411.profile16467,MergedCutProfiles.Batch411.profile16468,MergedCutProfiles.Batch411.profile16469,MergedCutProfiles.Batch411.profile16470,MergedCutProfiles.Batch411.profile16471,MergedCutProfiles.Batch411.profile16472,MergedCutProfiles.Batch411.profile16473,MergedCutProfiles.Batch411.profile16474,MergedCutProfiles.Batch411.profile16475,MergedCutProfiles.Batch411.profile16476]⟩
theorem profilesValid2619 : retention2619.ProfilesValid := by
  change ∀ j : Fin 16, (retention2619.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch411.valid16461
  · exact MergedCutProfiles.Batch411.valid16462
  · exact MergedCutProfiles.Batch411.valid16463
  · exact MergedCutProfiles.Batch411.valid16464
  · exact MergedCutProfiles.Batch411.valid16465
  · exact MergedCutProfiles.Batch411.valid16466
  · exact MergedCutProfiles.Batch411.valid16467
  · exact MergedCutProfiles.Batch411.valid16468
  · exact MergedCutProfiles.Batch411.valid16469
  · exact MergedCutProfiles.Batch411.valid16470
  · exact MergedCutProfiles.Batch411.valid16471
  · exact MergedCutProfiles.Batch411.valid16472
  · exact MergedCutProfiles.Batch411.valid16473
  · exact MergedCutProfiles.Batch411.valid16474
  · exact MergedCutProfiles.Batch411.valid16475
  · exact MergedCutProfiles.Batch411.valid16476
theorem numericValid2619 : retention2619.NumericValid := by decide +kernel
def certificate2619 : RatCutBinCertificate := ⟨⟨retention2619,(1147499597416809633/500000000000000000),(24651154762240763/125000000000000000),(8155537656678971133/500000000000000000),(94498107574152091661/250000000000000000),(624922327839959683/500000000000000000)⟩,(62193564122656627/62500000000000000),(353317939518720927/1000000000000000000),(545096480515327/1953125000000000),(208342266752737781/1000000000000000000)⟩
theorem valid2619 : certificate2619.Valid := by decide +kernel
theorem sound2619 : certificate2619.Sound := rat_cut_bin_certificate_sound certificate2619 profilesValid2619 numericValid2619 valid2619

def retention2620 : RatCutRetentionCertificate := ⟨(123/2000),(31/500),(11153431501695381243/23102356905764287544),(8111936519043882443/1000000000000000000),(21/20),(13289796022796081132025568171552459973871/12979098430470211908800000000000000000000),false,MergedCutProfiles.Batch411.profile16477,(fun _ => MergedCutProfiles.Batch411.profile16477)⟩
theorem profilesValid2620 : retention2620.ProfilesValid := by
  exact MergedCutProfiles.Batch411.valid16477
theorem numericValid2620 : retention2620.NumericValid := by decide +kernel
def certificate2620 : RatCutBinCertificate := ⟨⟨retention2620,(1147499597416809633/500000000000000000),(24651154762240763/125000000000000000),(8155537656678971133/500000000000000000),(94498107574152091661/250000000000000000),(497400709720571487/500000000000000000)⟩,(62193564122656627/62500000000000000),(193633926696003119/500000000000000000),(61338226123032267/250000000000000000),(26011341382454903/125000000000000000)⟩
theorem valid2620 : certificate2620.Valid := by decide +kernel
theorem sound2620 : certificate2620.Sound := rat_cut_bin_certificate_sound certificate2620 profilesValid2620 numericValid2620 valid2620

def retention2621 : RatCutRetentionCertificate := ⟨(123/2000),(31/500),(1436423953703531624/2887794613220535943),(11153431501695381243/1000000000000000000),(21/20),(5962065467479088717804751251722811944917/5948496800904203329600000000000000000000),false,MergedCutProfiles.Batch411.profile16478,(fun _ => MergedCutProfiles.Batch411.profile16478)⟩
theorem profilesValid2621 : retention2621.ProfilesValid := by
  exact MergedCutProfiles.Batch411.valid16478
theorem numericValid2621 : retention2621.NumericValid := by decide +kernel
def certificate2621 : RatCutBinCertificate := ⟨⟨retention2621,(1147499597416809633/500000000000000000),(24651154762240763/125000000000000000),(8155537656678971133/500000000000000000),(94498107574152091661/250000000000000000),(973144627429105857/1000000000000000000)⟩,(62193564122656627/62500000000000000),(194145119852934969/500000000000000000),(122192218353134207/500000000000000000),(4176095434054309/20000000000000000)⟩
theorem valid2621 : certificate2621.Valid := by decide +kernel
theorem sound2621 : certificate2621.Sound := rat_cut_bin_certificate_sound certificate2621 profilesValid2621 numericValid2621 valid2621

def retention2622 : RatCutRetentionCertificate := ⟨(123/2000),(31/500),(1/2),(179552994212941453/15625000000000000),(21/20),(286609338677193681045513228439549079279/287284790740706324800000000000000000000),false,MergedCutProfiles.Batch411.profile16479,(fun _ => MergedCutProfiles.Batch411.profile16479)⟩
theorem profilesValid2622 : retention2622.ProfilesValid := by
  exact MergedCutProfiles.Batch411.valid16479
theorem numericValid2622 : retention2622.NumericValid := by decide +kernel
def certificate2622 : RatCutBinCertificate := ⟨⟨retention2622,(1147499597416809633/500000000000000000),(24651154762240763/125000000000000000),(8155537656678971133/500000000000000000),(94498107574152091661/250000000000000000),(968512482712888301/1000000000000000000)⟩,(62193564122656627/62500000000000000),(389548658143499221/1000000000000000000),(243196077534417741/1000000000000000000),(51829784676762823/250000000000000000)⟩
theorem valid2622 : certificate2622.Valid := by decide +kernel
theorem sound2622 : certificate2622.Sound := rat_cut_bin_certificate_sound certificate2622 profilesValid2622 numericValid2622 valid2622

def retention2623 : RatCutRetentionCertificate := ⟨(123/2000),(31/500),(5214024259950505065/11551178452882143772),(1248421938625348219/250000000000000000),(21/20),(531116113451019897509716972330862423079/499368775450139287600000000000000000000),false,MergedCutProfiles.Batch412.profile16480,(fun _ => MergedCutProfiles.Batch412.profile16480)⟩
theorem profilesValid2623 : retention2623.ProfilesValid := by
  exact MergedCutProfiles.Batch412.valid16480
theorem numericValid2623 : retention2623.NumericValid := by decide +kernel
def certificate2623 : RatCutBinCertificate := ⟨⟨retention2623,(1272969737916809633/500000000000000000),(24651154762240763/125000000000000000),(8155537656678971133/500000000000000000),(94498107574152091661/250000000000000000),(257812731250170637/250000000000000000)⟩,(497280112320816079/500000000000000000),(226173053364179513/1000000000000000000),(87495178644683937/200000000000000000),(359727548879131553/1000000000000000000)⟩
theorem valid2623 : certificate2623.Valid := by decide +kernel
theorem sound2623 : certificate2623.Sound := rat_cut_bin_certificate_sound certificate2623 profilesValid2623 numericValid2623 valid2623

def retention2624 : RatCutRetentionCertificate := ⟨(123/2000),(31/500),(2851250772263420591/5775589226441071886),(1042804851990101013/100000000000000000),1,(10319998456219504284202437369908718731/10428048519901010130000000000000000000),false,MergedCutProfiles.Batch412.profile16481,(fun _ => MergedCutProfiles.Batch412.profile16481)⟩
theorem profilesValid2624 : retention2624.ProfilesValid := by
  exact MergedCutProfiles.Batch412.valid16481
theorem numericValid2624 : retention2624.NumericValid := by decide +kernel
def certificate2624 : RatCutBinCertificate := ⟨⟨retention2624,(1272969737916809633/500000000000000000),(24651154762240763/125000000000000000),(8155537656678971133/500000000000000000),(94498107574152091661/250000000000000000),(958855265754378139/1000000000000000000)⟩,(497280112320816079/500000000000000000),(48649922219186369/200000000000000000),(412775606260235979/1000000000000000000),(360391239655764659/1000000000000000000)⟩
theorem valid2624 : certificate2624.Valid := by decide +kernel
theorem sound2624 : certificate2624.Sound := rat_cut_bin_certificate_sound certificate2624 profilesValid2624 numericValid2624 valid2624

def retention2625 : RatCutRetentionCertificate := ⟨(123/2000),(31/500),(2879763279986054797/5775589226441071886),(2851250772263420591/250000000000000000),1,(44812031626098182026966785892888816623/45620012356214729456000000000000000000),false,MergedCutProfiles.Batch412.profile16482,(fun _ => MergedCutProfiles.Batch412.profile16482)⟩
theorem profilesValid2625 : retention2625.ProfilesValid := by
  exact MergedCutProfiles.Batch412.valid16482
theorem numericValid2625 : retention2625.NumericValid := by decide +kernel
def certificate2625 : RatCutBinCertificate := ⟨⟨retention2625,(1272969737916809633/500000000000000000),(24651154762240763/125000000000000000),(8155537656678971133/500000000000000000),(94498107574152091661/250000000000000000),(47575288969833767/50000000000000000)⟩,(497280112320816079/500000000000000000),(245128485336085839/1000000000000000000),(410131437570147399/1000000000000000000),(89535114489712297/250000000000000000)⟩
theorem valid2625 : certificate2625.Valid := by decide +kernel
theorem sound2625 : certificate2625.Sound := rat_cut_bin_certificate_sound certificate2625 profilesValid2625 numericValid2625 valid2625

def retention2626 : RatCutRetentionCertificate := ⟨(123/2000),(31/500),(1/2),(2879763279986054797/250000000000000000),1,(11286863154560263965315479888911437183/11519053119944219188000000000000000000),false,MergedCutProfiles.Batch411.profile16479,(fun _ => MergedCutProfiles.Batch411.profile16479)⟩
theorem profilesValid2626 : retention2626.ProfilesValid := by
  exact MergedCutProfiles.Batch411.valid16479
theorem numericValid2626 : retention2626.NumericValid := by decide +kernel
def certificate2626 : RatCutBinCertificate := ⟨⟨retention2626,(1272969737916809633/500000000000000000),(24651154762240763/125000000000000000),(8155537656678971133/500000000000000000),(94498107574152091661/250000000000000000),(949059860436205909/1000000000000000000)⟩,(497280112320816079/500000000000000000),(61440057739044193/250000000000000000),(409245564792963041/1000000000000000000),(11149719285863161/31250000000000000)⟩
theorem valid2626 : certificate2626.Valid := by decide +kernel
theorem sound2626 : certificate2626.Sound := rat_cut_bin_certificate_sound certificate2626 profilesValid2626 numericValid2626 valid2626

def retention2627 : RatCutRetentionCertificate := ⟨(31/500),(1/16),(939338018005505913/22663700226962782985),(465018820794804907/500000000000000000),(53/20),(41688158069072917483/20000000000000000000),true,MergedCutProfiles.Batch412.profile16483,![MergedCutProfiles.Batch412.profile16483,MergedCutProfiles.Batch412.profile16484,MergedCutProfiles.Batch412.profile16485,MergedCutProfiles.Batch412.profile16486,MergedCutProfiles.Batch412.profile16487,MergedCutProfiles.Batch412.profile16488,MergedCutProfiles.Batch412.profile16489,MergedCutProfiles.Batch412.profile16490,MergedCutProfiles.Batch412.profile16491,MergedCutProfiles.Batch412.profile16492,MergedCutProfiles.Batch412.profile16493,MergedCutProfiles.Batch412.profile16494,MergedCutProfiles.Batch412.profile16495,MergedCutProfiles.Batch412.profile16496,MergedCutProfiles.Batch412.profile16497,MergedCutProfiles.Batch412.profile16498]⟩
theorem profilesValid2627 : retention2627.ProfilesValid := by
  change ∀ j : Fin 16, (retention2627.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch412.valid16483
  · exact MergedCutProfiles.Batch412.valid16484
  · exact MergedCutProfiles.Batch412.valid16485
  · exact MergedCutProfiles.Batch412.valid16486
  · exact MergedCutProfiles.Batch412.valid16487
  · exact MergedCutProfiles.Batch412.valid16488
  · exact MergedCutProfiles.Batch412.valid16489
  · exact MergedCutProfiles.Batch412.valid16490
  · exact MergedCutProfiles.Batch412.valid16491
  · exact MergedCutProfiles.Batch412.valid16492
  · exact MergedCutProfiles.Batch412.valid16493
  · exact MergedCutProfiles.Batch412.valid16494
  · exact MergedCutProfiles.Batch412.valid16495
  · exact MergedCutProfiles.Batch412.valid16496
  · exact MergedCutProfiles.Batch412.valid16497
  · exact MergedCutProfiles.Batch412.valid16498
theorem numericValid2627 : retention2627.NumericValid := by decide +kernel
def certificate2627 : RatCutBinCertificate := ⟨⟨retention2627,(2300964834594250959/1000000000000000000),(50258241146397749/250000000000000000),(2057940274574033059/125000000000000000),(374284969214866128027/1000000000000000000),(1004967780462835437/500000000000000000)⟩,(497529304158783303/500000000000000000),(14679673967879219/50000000000000000),(173281518894523851/500000000000000000),(6243964613661023/31250000000000000)⟩
theorem valid2627 : certificate2627.Valid := by decide +kernel
theorem sound2627 : certificate2627.Sound := rat_cut_bin_certificate_sound certificate2627 profilesValid2627 numericValid2627 valid2627

def certificates : List RatCutBinCertificate := [certificate2616,certificate2617,certificate2618,certificate2619,certificate2620,certificate2621,certificate2622,certificate2623,certificate2624,certificate2625,certificate2626,certificate2627]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound2616,List.forall_mem_cons.mpr ⟨sound2617,List.forall_mem_cons.mpr ⟨sound2618,List.forall_mem_cons.mpr ⟨sound2619,List.forall_mem_cons.mpr ⟨sound2620,List.forall_mem_cons.mpr ⟨sound2621,List.forall_mem_cons.mpr ⟨sound2622,List.forall_mem_cons.mpr ⟨sound2623,List.forall_mem_cons.mpr ⟨sound2624,List.forall_mem_cons.mpr ⟨sound2625,List.forall_mem_cons.mpr ⟨sound2626,List.forall_mem_cons.mpr ⟨sound2627,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch218
