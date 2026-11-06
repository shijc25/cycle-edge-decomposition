import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch305
import Cycle12.MergedCutProfiles.Batch306
import Cycle12.MergedCutProfiles.Batch307
import Cycle12.MergedCutProfiles.Batch439
import Cycle12.MergedCutProfiles.Batch440
import Cycle12.MergedCutProfiles.Batch559
import Cycle12.MergedCutProfiles.Batch560
import Cycle12.MergedCutProfiles.Batch561

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch303

def retention3636 : RatCutRetentionCertificate := ⟨(67/1000),(27/400),(4648888678734769198/9412525033197477019),(5420128006224398427/250000000000000000),1,(86897436282228386306460972447069924287/86722048099590374832000000000000000000),false,MergedCutProfiles.Batch559.profile22367,(fun _ => MergedCutProfiles.Batch559.profile22367)⟩
theorem profilesValid3636 : retention3636.ProfilesValid := by
  exact MergedCutProfiles.Batch559.valid22367
theorem numericValid3636 : retention3636.NumericValid := by decide +kernel
def certificate3636 : RatCutBinCertificate := ⟨⟨retention3636,(2353563829462153949/1000000000000000000),(121143195939341811/500000000000000000),(452907603621399993/25000000000000000),(213836632946619844371/250000000000000000),(970545581216311129/1000000000000000000)⟩,(249475408061513141/250000000000000000),(121676064949481663/1000000000000000000),(620037585752495299/1000000000000000000),(71843065682711641/125000000000000000)⟩
theorem valid3636 : certificate3636.Valid := by decide +kernel
theorem sound3636 : certificate3636.Sound := rat_cut_bin_certificate_sound certificate3636 profilesValid3636 numericValid3636 valid3636

def retention3637 : RatCutRetentionCertificate := ⟨(67/1000),(27/400),(4695377565522116890/9412525033197477019),(2324444339367384599/100000000000000000),1,(23084738247894756722516670010381474851/23244443393673845990000000000000000000),false,MergedCutProfiles.Batch559.profile22368,(fun _ => MergedCutProfiles.Batch559.profile22368)⟩
theorem profilesValid3637 : retention3637.ProfilesValid := by
  exact MergedCutProfiles.Batch559.valid22368
theorem numericValid3637 : retention3637.NumericValid := by decide +kernel
def certificate3637 : RatCutBinCertificate := ⟨⟨retention3637,(2353563829462153949/1000000000000000000),(121143195939341811/500000000000000000),(452907603621399993/25000000000000000),(213836632946619844371/250000000000000000),(480826255432996263/500000000000000000)⟩,(249475408061513141/250000000000000000),(61400644121525407/500000000000000000),(617725991330862793/1000000000000000000),(569206797977515451/1000000000000000000)⟩
theorem valid3637 : certificate3637.Valid := by decide +kernel
theorem sound3637 : certificate3637.Sound := rat_cut_bin_certificate_sound certificate3637 profilesValid3637 numericValid3637 valid3637

def retention3638 : RatCutRetentionCertificate := ⟨(67/1000),(27/400),(1/2),(469537756552211689/20000000000000000),1,(93059476006407277096692907421281910919/93907551310442337800000000000000000000),false,MergedCutProfiles.Batch305.profile12226,(fun _ => MergedCutProfiles.Batch305.profile12226)⟩
theorem profilesValid3638 : retention3638.ProfilesValid := by
  exact MergedCutProfiles.Batch305.valid12226
theorem numericValid3638 : retention3638.NumericValid := by decide +kernel
def certificate3638 : RatCutBinCertificate := ⟨⟨retention3638,(2353563829462153949/1000000000000000000),(121143195939341811/500000000000000000),(452907603621399993/25000000000000000),(213836632946619844371/250000000000000000),(959492235620660659/1000000000000000000)⟩,(249475408061513141/250000000000000000),(123077772588872251/1000000000000000000),(617159356623637333/1000000000000000000),(283840470563867943/500000000000000000)⟩
theorem valid3638 : certificate3638.Valid := by decide +kernel
theorem sound3638 : certificate3638.Sound := rat_cut_bin_certificate_sound certificate3638 profilesValid3638 numericValid3638 valid3638

def retention3639 : RatCutRetentionCertificate := ⟨(27/400),(17/250),(242875796818519509/11555922301585115699),(961884343835720827/1000000000000000000),(27/10),(112195274216810493903/51200000000000000000),true,MergedCutProfiles.Batch559.profile22369,![MergedCutProfiles.Batch559.profile22369,MergedCutProfiles.Batch559.profile22370,MergedCutProfiles.Batch559.profile22371,MergedCutProfiles.Batch559.profile22372,MergedCutProfiles.Batch559.profile22373,MergedCutProfiles.Batch559.profile22374,MergedCutProfiles.Batch559.profile22375,MergedCutProfiles.Batch559.profile22376,MergedCutProfiles.Batch559.profile22377,MergedCutProfiles.Batch559.profile22378,MergedCutProfiles.Batch559.profile22379,MergedCutProfiles.Batch559.profile22380,MergedCutProfiles.Batch439.profile17592,MergedCutProfiles.Batch559.profile22381,MergedCutProfiles.Batch559.profile22382,MergedCutProfiles.Batch559.profile22383]⟩
theorem profilesValid3639 : retention3639.ProfilesValid := by
  change ∀ j : Fin 16, (retention3639.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch559.valid22369
  · exact MergedCutProfiles.Batch559.valid22370
  · exact MergedCutProfiles.Batch559.valid22371
  · exact MergedCutProfiles.Batch559.valid22372
  · exact MergedCutProfiles.Batch559.valid22373
  · exact MergedCutProfiles.Batch559.valid22374
  · exact MergedCutProfiles.Batch559.valid22375
  · exact MergedCutProfiles.Batch559.valid22376
  · exact MergedCutProfiles.Batch559.valid22377
  · exact MergedCutProfiles.Batch559.valid22378
  · exact MergedCutProfiles.Batch559.valid22379
  · exact MergedCutProfiles.Batch559.valid22380
  · exact MergedCutProfiles.Batch439.valid17592
  · exact MergedCutProfiles.Batch559.valid22381
  · exact MergedCutProfiles.Batch559.valid22382
  · exact MergedCutProfiles.Batch559.valid22383
theorem numericValid3639 : retention3639.NumericValid := by decide +kernel
def certificate3639 : RatCutBinCertificate := ⟨⟨retention3639,(2322531896774833293/1000000000000000000),(123364672097640231/500000000000000000),(18294995889297718301/1000000000000000000),(848395165509429942467/1000000000000000000),(1053367472586151633/500000000000000000)⟩,(124740540082341501/125000000000000000),(265844478043893541/1000000000000000000),(381896610154826323/1000000000000000000),(114282461130579883/500000000000000000)⟩
theorem valid3639 : certificate3639.Valid := by decide +kernel
theorem sound3639 : certificate3639.Sound := rat_cut_bin_certificate_sound certificate3639 profilesValid3639 numericValid3639 valid3639

def retention3640 : RatCutRetentionCertificate := ⟨(27/400),(17/250),(278631223000000000/11555922301585115699),(242875796818519509/250000000000000000),(27/10),(21848084463464716563/10000000000000000000),true,MergedCutProfiles.Batch559.profile22384,![MergedCutProfiles.Batch559.profile22384,MergedCutProfiles.Batch559.profile22385,MergedCutProfiles.Batch559.profile22386,MergedCutProfiles.Batch559.profile22387,MergedCutProfiles.Batch559.profile22388,MergedCutProfiles.Batch559.profile22389,MergedCutProfiles.Batch559.profile22390,MergedCutProfiles.Batch559.profile22391,MergedCutProfiles.Batch559.profile22392,MergedCutProfiles.Batch559.profile22393,MergedCutProfiles.Batch559.profile22394,MergedCutProfiles.Batch559.profile22395,MergedCutProfiles.Batch559.profile22396,MergedCutProfiles.Batch559.profile22397,MergedCutProfiles.Batch559.profile22398,MergedCutProfiles.Batch559.profile22399]⟩
theorem profilesValid3640 : retention3640.ProfilesValid := by
  change ∀ j : Fin 16, (retention3640.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch559.valid22384
  · exact MergedCutProfiles.Batch559.valid22385
  · exact MergedCutProfiles.Batch559.valid22386
  · exact MergedCutProfiles.Batch559.valid22387
  · exact MergedCutProfiles.Batch559.valid22388
  · exact MergedCutProfiles.Batch559.valid22389
  · exact MergedCutProfiles.Batch559.valid22390
  · exact MergedCutProfiles.Batch559.valid22391
  · exact MergedCutProfiles.Batch559.valid22392
  · exact MergedCutProfiles.Batch559.valid22393
  · exact MergedCutProfiles.Batch559.valid22394
  · exact MergedCutProfiles.Batch559.valid22395
  · exact MergedCutProfiles.Batch559.valid22396
  · exact MergedCutProfiles.Batch559.valid22397
  · exact MergedCutProfiles.Batch559.valid22398
  · exact MergedCutProfiles.Batch559.valid22399
theorem numericValid3640 : retention3640.NumericValid := by decide +kernel
def certificate3640 : RatCutBinCertificate := ⟨⟨retention3640,(2322531896774833293/1000000000000000000),(123364672097640231/500000000000000000),(18294995889297718301/1000000000000000000),(848395165509429942467/1000000000000000000),(2100229535734062487/1000000000000000000)⟩,(124740540082341501/125000000000000000),(132775656795691461/500000000000000000),(191142369414274123/500000000000000000),(228776302635268177/1000000000000000000)⟩
theorem valid3640 : certificate3640.Valid := by decide +kernel
theorem sound3640 : certificate3640.Sound := rat_cut_bin_certificate_sound certificate3640 profilesValid3640 numericValid3640 valid3640

def retention3641 : RatCutRetentionCertificate := ⟨(27/400),(17/250),(68356534416437511/2719040541549438988),(278631223/250000000),(12/5),(8667632930331662391/4000000000000000000),true,MergedCutProfiles.Batch560.profile22400,![MergedCutProfiles.Batch560.profile22400,MergedCutProfiles.Batch560.profile22401,MergedCutProfiles.Batch560.profile22402,MergedCutProfiles.Batch560.profile22403,MergedCutProfiles.Batch559.profile22374,MergedCutProfiles.Batch560.profile22404,MergedCutProfiles.Batch560.profile22405,MergedCutProfiles.Batch560.profile22406,MergedCutProfiles.Batch560.profile22407,MergedCutProfiles.Batch560.profile22408,MergedCutProfiles.Batch560.profile22409,MergedCutProfiles.Batch560.profile22410,MergedCutProfiles.Batch560.profile22411,MergedCutProfiles.Batch560.profile22412,MergedCutProfiles.Batch560.profile22413,MergedCutProfiles.Batch560.profile22414]⟩
theorem profilesValid3641 : retention3641.ProfilesValid := by
  change ∀ j : Fin 16, (retention3641.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch560.valid22400
  · exact MergedCutProfiles.Batch560.valid22401
  · exact MergedCutProfiles.Batch560.valid22402
  · exact MergedCutProfiles.Batch560.valid22403
  · exact MergedCutProfiles.Batch559.valid22374
  · exact MergedCutProfiles.Batch560.valid22404
  · exact MergedCutProfiles.Batch560.valid22405
  · exact MergedCutProfiles.Batch560.valid22406
  · exact MergedCutProfiles.Batch560.valid22407
  · exact MergedCutProfiles.Batch560.valid22408
  · exact MergedCutProfiles.Batch560.valid22409
  · exact MergedCutProfiles.Batch560.valid22410
  · exact MergedCutProfiles.Batch560.valid22411
  · exact MergedCutProfiles.Batch560.valid22412
  · exact MergedCutProfiles.Batch560.valid22413
  · exact MergedCutProfiles.Batch560.valid22414
theorem numericValid3641 : retention3641.NumericValid := by decide +kernel
def certificate3641 : RatCutBinCertificate := ⟨⟨retention3641,(2322531896774833293/1000000000000000000),(123364672097640231/500000000000000000),(18294995889297718301/1000000000000000000),(848395165509429942467/1000000000000000000),(2091727140109222877/1000000000000000000)⟩,(124740540082341501/125000000000000000),(252243532401066051/1000000000000000000),(50030761206168817/125000000000000000),(262452076469206429/1000000000000000000)⟩
theorem valid3641 : certificate3641.Valid := by decide +kernel
theorem sound3641 : certificate3641.Sound := rat_cut_bin_certificate_sound certificate3641 profilesValid3641 numericValid3641 valid3641

def retention3642 : RatCutRetentionCertificate := ⟨(27/400),(17/250),(131184980829964175/3301692086167175914),(1162061085079437687/1000000000000000000),(23/10),(168513166249529631237/80000000000000000000),true,MergedCutProfiles.Batch560.profile22415,![MergedCutProfiles.Batch560.profile22415,MergedCutProfiles.Batch560.profile22416,MergedCutProfiles.Batch560.profile22417,MergedCutProfiles.Batch439.profile17564,MergedCutProfiles.Batch560.profile22418,MergedCutProfiles.Batch560.profile22419,MergedCutProfiles.Batch560.profile22420,MergedCutProfiles.Batch560.profile22421,MergedCutProfiles.Batch560.profile22422,MergedCutProfiles.Batch560.profile22423,MergedCutProfiles.Batch560.profile22424,MergedCutProfiles.Batch560.profile22425,MergedCutProfiles.Batch560.profile22426,MergedCutProfiles.Batch560.profile22427,MergedCutProfiles.Batch560.profile22428,MergedCutProfiles.Batch560.profile22429]⟩
theorem profilesValid3642 : retention3642.ProfilesValid := by
  change ∀ j : Fin 16, (retention3642.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch560.valid22415
  · exact MergedCutProfiles.Batch560.valid22416
  · exact MergedCutProfiles.Batch560.valid22417
  · exact MergedCutProfiles.Batch439.valid17564
  · exact MergedCutProfiles.Batch560.valid22418
  · exact MergedCutProfiles.Batch560.valid22419
  · exact MergedCutProfiles.Batch560.valid22420
  · exact MergedCutProfiles.Batch560.valid22421
  · exact MergedCutProfiles.Batch560.valid22422
  · exact MergedCutProfiles.Batch560.valid22423
  · exact MergedCutProfiles.Batch560.valid22424
  · exact MergedCutProfiles.Batch560.valid22425
  · exact MergedCutProfiles.Batch560.valid22426
  · exact MergedCutProfiles.Batch560.valid22427
  · exact MergedCutProfiles.Batch560.valid22428
  · exact MergedCutProfiles.Batch560.valid22429
theorem numericValid3642 : retention3642.NumericValid := by decide +kernel
def certificate3642 : RatCutBinCertificate := ⟨⟨retention3642,(2322531896774833293/1000000000000000000),(123364672097640231/500000000000000000),(18294995889297718301/1000000000000000000),(848395165509429942467/1000000000000000000),(406873204990940273/200000000000000000)⟩,(124740540082341501/125000000000000000),(255245355596544313/1000000000000000000),(198067608891474289/500000000000000000),(65651608765936179/250000000000000000)⟩
theorem valid3642 : certificate3642.Valid := by decide +kernel
theorem sound3642 : certificate3642.Sound := rat_cut_bin_certificate_sound certificate3642 profilesValid3642 numericValid3642 valid3642

def retention3643 : RatCutRetentionCertificate := ⟨(27/400),(17/250),(4512341512487934063/23111844603170231398),(36731794632389969/20000000000000000),(17/10),(42311891642000814077/25600000000000000000),true,MergedCutProfiles.Batch560.profile22430,![MergedCutProfiles.Batch560.profile22430,MergedCutProfiles.Batch560.profile22431,MergedCutProfiles.Batch305.profile12233,MergedCutProfiles.Batch560.profile22432,MergedCutProfiles.Batch306.profile12279,MergedCutProfiles.Batch560.profile22433,MergedCutProfiles.Batch440.profile17602,MergedCutProfiles.Batch560.profile22434,MergedCutProfiles.Batch306.profile12241,MergedCutProfiles.Batch560.profile22435,MergedCutProfiles.Batch560.profile22436,MergedCutProfiles.Batch560.profile22437,MergedCutProfiles.Batch560.profile22438,MergedCutProfiles.Batch560.profile22439,MergedCutProfiles.Batch561.profile22440,MergedCutProfiles.Batch561.profile22441]⟩
theorem profilesValid3643 : retention3643.ProfilesValid := by
  change ∀ j : Fin 16, (retention3643.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch560.valid22430
  · exact MergedCutProfiles.Batch560.valid22431
  · exact MergedCutProfiles.Batch305.valid12233
  · exact MergedCutProfiles.Batch560.valid22432
  · exact MergedCutProfiles.Batch306.valid12279
  · exact MergedCutProfiles.Batch560.valid22433
  · exact MergedCutProfiles.Batch440.valid17602
  · exact MergedCutProfiles.Batch560.valid22434
  · exact MergedCutProfiles.Batch306.valid12241
  · exact MergedCutProfiles.Batch560.valid22435
  · exact MergedCutProfiles.Batch560.valid22436
  · exact MergedCutProfiles.Batch560.valid22437
  · exact MergedCutProfiles.Batch560.valid22438
  · exact MergedCutProfiles.Batch560.valid22439
  · exact MergedCutProfiles.Batch561.valid22440
  · exact MergedCutProfiles.Batch561.valid22441
theorem numericValid3643 : retention3643.NumericValid := by decide +kernel
def certificate3643 : RatCutBinCertificate := ⟨⟨retention3643,(2322531896774833293/1000000000000000000),(123364672097640231/500000000000000000),(18294995889297718301/1000000000000000000),(848395165509429942467/1000000000000000000),(49986119465593073/31250000000000000)⟩,(124740540082341501/125000000000000000),(139806276414631951/500000000000000000),(364023608559608607/1000000000000000000),(52511206149625839/200000000000000000)⟩
theorem valid3643 : certificate3643.Valid := by decide +kernel
theorem sound3643 : certificate3643.Sound := rat_cut_bin_certificate_sound certificate3643 profilesValid3643 numericValid3643 valid3643

def retention3644 : RatCutRetentionCertificate := ⟨(27/400),(17/250),(21235872167455315429/46223689206340462796),(4512341512487934063/500000000000000000),(21/20),(3871369936508210840697487157109790693991/3609873209990347250400000000000000000000),false,MergedCutProfiles.Batch561.profile22442,(fun _ => MergedCutProfiles.Batch561.profile22442)⟩
theorem profilesValid3644 : retention3644.ProfilesValid := by
  exact MergedCutProfiles.Batch561.valid22442
theorem numericValid3644 : retention3644.NumericValid := by decide +kernel
def certificate3644 : RatCutBinCertificate := ⟨⟨retention3644,(2322531896774833293/1000000000000000000),(123364672097640231/500000000000000000),(18294995889297718301/1000000000000000000),(848395165509429942467/1000000000000000000),(51977507447433869/50000000000000000)⟩,(124740540082341501/125000000000000000),(83798280031755269/250000000000000000),(149207877784689771/500000000000000000),(266904813659756841/1000000000000000000)⟩
theorem valid3644 : certificate3644.Valid := by decide +kernel
theorem sound3644 : certificate3644.Sound := rat_cut_bin_certificate_sound certificate3644 profilesValid3644 numericValid3644 valid3644

def retention3645 : RatCutRetentionCertificate := ⟨(27/400),(17/250),(22995406576389699819/46223689206340462796),(21235872167455315429/1000000000000000000),1,(4224978821874448661158608817077451089/4247174433491063085800000000000000000),false,MergedCutProfiles.Batch561.profile22443,(fun _ => MergedCutProfiles.Batch561.profile22443)⟩
theorem profilesValid3645 : retention3645.ProfilesValid := by
  exact MergedCutProfiles.Batch561.valid22443
theorem numericValid3645 : retention3645.NumericValid := by decide +kernel
def certificate3645 : RatCutBinCertificate := ⟨⟨retention3645,(2322531896774833293/1000000000000000000),(123364672097640231/500000000000000000),(18294995889297718301/1000000000000000000),(848395165509429942467/1000000000000000000),(240862887500936763/250000000000000000)⟩,(124740540082341501/125000000000000000),(346601057020690773/1000000000000000000),(17883793831797467/62500000000000000),(52630643749749001/200000000000000000)⟩
theorem valid3645 : certificate3645.Valid := by decide +kernel
theorem sound3645 : certificate3645.Sound := rat_cut_bin_certificate_sound certificate3645 profilesValid3645 numericValid3645 valid3645

def retention3646 : RatCutRetentionCertificate := ⟨(27/400),(17/250),(1/2),(22995406576389699819/1000000000000000000),1,(18226137653549713638099474332397971023/18396325261111759855200000000000000000),false,MergedCutProfiles.Batch307.profile12294,(fun _ => MergedCutProfiles.Batch307.profile12294)⟩
theorem profilesValid3646 : retention3646.ProfilesValid := by
  exact MergedCutProfiles.Batch307.valid12294
theorem numericValid3646 : retention3646.NumericValid := by decide +kernel
def certificate3646 : RatCutBinCertificate := ⟨⟨retention3646,(2322531896774833293/1000000000000000000),(123364672097640231/500000000000000000),(18294995889297718301/1000000000000000000),(848395165509429942467/1000000000000000000),(479713190009586677/500000000000000000)⟩,(124740540082341501/125000000000000000),(17359977534919683/50000000000000000),(57101434498625821/200000000000000000),(52478032191221829/200000000000000000)⟩
theorem valid3646 : certificate3646.Valid := by decide +kernel
theorem sound3646 : certificate3646.Sound := rat_cut_bin_certificate_sound certificate3646 profilesValid3646 numericValid3646 valid3646

def retention3647 : RatCutRetentionCertificate := ⟨(27/400),(17/250),(21123810384156213931/46223689206340462796),(4104041610675860181/500000000000000000),1,(34551375237817095784056951028582904951/32832332885406881448000000000000000000),false,MergedCutProfiles.Batch561.profile22444,(fun _ => MergedCutProfiles.Batch561.profile22444)⟩
theorem profilesValid3647 : retention3647.ProfilesValid := by
  exact MergedCutProfiles.Batch561.valid22444
theorem numericValid3647 : retention3647.NumericValid := by decide +kernel
def certificate3647 : RatCutBinCertificate := ⟨⟨retention3647,(2361128514774833293/1000000000000000000),(123364672097640231/500000000000000000),(18294995889297718301/1000000000000000000),(848395165509429942467/1000000000000000000),(1020514516892939997/1000000000000000000)⟩,(199577960609044837/200000000000000000),(14472413613231347/125000000000000000),(316149327747837957/500000000000000000),(572612465891026403/1000000000000000000)⟩
theorem valid3647 : certificate3647.Valid := by decide +kernel
theorem sound3647 : certificate3647.Sound := rat_cut_bin_certificate_sound certificate3647 profilesValid3647 numericValid3647 valid3647

def certificates : List RatCutBinCertificate := [certificate3636,certificate3637,certificate3638,certificate3639,certificate3640,certificate3641,certificate3642,certificate3643,certificate3644,certificate3645,certificate3646,certificate3647]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound3636,List.forall_mem_cons.mpr ⟨sound3637,List.forall_mem_cons.mpr ⟨sound3638,List.forall_mem_cons.mpr ⟨sound3639,List.forall_mem_cons.mpr ⟨sound3640,List.forall_mem_cons.mpr ⟨sound3641,List.forall_mem_cons.mpr ⟨sound3642,List.forall_mem_cons.mpr ⟨sound3643,List.forall_mem_cons.mpr ⟨sound3644,List.forall_mem_cons.mpr ⟨sound3645,List.forall_mem_cons.mpr ⟨sound3646,List.forall_mem_cons.mpr ⟨sound3647,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch303
