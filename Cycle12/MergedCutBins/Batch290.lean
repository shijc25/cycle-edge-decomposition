import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch534
import Cycle12.MergedCutProfiles.Batch535

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch290

def retention3480 : RatCutRetentionCertificate := ⟨(249/4000),(1/16),(911330029488777229/56659250567406957463),(225576739972469611/250000000000000000),(29/10),(22219962973551077969/10000000000000000000),true,MergedCutProfiles.Batch534.profile21361,![MergedCutProfiles.Batch534.profile21361,MergedCutProfiles.Batch534.profile21362,MergedCutProfiles.Batch534.profile21363,MergedCutProfiles.Batch534.profile21364,MergedCutProfiles.Batch534.profile21365,MergedCutProfiles.Batch534.profile21366,MergedCutProfiles.Batch534.profile21367,MergedCutProfiles.Batch534.profile21368,MergedCutProfiles.Batch534.profile21369,MergedCutProfiles.Batch534.profile21370,MergedCutProfiles.Batch534.profile21371,MergedCutProfiles.Batch534.profile21372,MergedCutProfiles.Batch534.profile21373,MergedCutProfiles.Batch534.profile21374,MergedCutProfiles.Batch534.profile21375,MergedCutProfiles.Batch534.profile21376]⟩
theorem profilesValid3480 : retention3480.ProfilesValid := by
  change ∀ j : Fin 16, (retention3480.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch534.valid21361
  · exact MergedCutProfiles.Batch534.valid21362
  · exact MergedCutProfiles.Batch534.valid21363
  · exact MergedCutProfiles.Batch534.valid21364
  · exact MergedCutProfiles.Batch534.valid21365
  · exact MergedCutProfiles.Batch534.valid21366
  · exact MergedCutProfiles.Batch534.valid21367
  · exact MergedCutProfiles.Batch534.valid21368
  · exact MergedCutProfiles.Batch534.valid21369
  · exact MergedCutProfiles.Batch534.valid21370
  · exact MergedCutProfiles.Batch534.valid21371
  · exact MergedCutProfiles.Batch534.valid21372
  · exact MergedCutProfiles.Batch534.valid21373
  · exact MergedCutProfiles.Batch534.valid21374
  · exact MergedCutProfiles.Batch534.valid21375
  · exact MergedCutProfiles.Batch534.valid21376
theorem numericValid3480 : retention3480.NumericValid := by decide +kernel
def certificate3480 : RatCutBinCertificate := ⟨⟨retention3480,(70023092426178137/31250000000000000),(50258241146397749/250000000000000000),(16542216660907816767/1000000000000000000),(938727443778951818319/1000000000000000000),(535754926877431161/250000000000000000)⟩,(499043685709745071/500000000000000000),(157689786931541791/500000000000000000),(4008300314919977/12500000000000000),(18435511029535947/100000000000000000)⟩
theorem valid3480 : certificate3480.Valid := by decide +kernel
theorem sound3480 : certificate3480.Sound := rat_cut_bin_certificate_sound certificate3480 profilesValid3480 numericValid3480 valid3480

def retention3481 : RatCutRetentionCertificate := ⟨(249/4000),(1/16),(1068606131056224624/56659250567406957463),(911330029488777229/1000000000000000000),(29/10),(177151890943643203207/80000000000000000000),true,MergedCutProfiles.Batch534.profile21377,![MergedCutProfiles.Batch534.profile21377,MergedCutProfiles.Batch534.profile21378,MergedCutProfiles.Batch534.profile21379,MergedCutProfiles.Batch534.profile21380,MergedCutProfiles.Batch534.profile21381,MergedCutProfiles.Batch534.profile21382,MergedCutProfiles.Batch534.profile21383,MergedCutProfiles.Batch534.profile21384,MergedCutProfiles.Batch534.profile21385,MergedCutProfiles.Batch534.profile21386,MergedCutProfiles.Batch534.profile21387,MergedCutProfiles.Batch534.profile21388,MergedCutProfiles.Batch534.profile21389,MergedCutProfiles.Batch534.profile21390,MergedCutProfiles.Batch534.profile21391,MergedCutProfiles.Batch534.profile21392]⟩
theorem profilesValid3481 : retention3481.ProfilesValid := by
  change ∀ j : Fin 16, (retention3481.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch534.valid21377
  · exact MergedCutProfiles.Batch534.valid21378
  · exact MergedCutProfiles.Batch534.valid21379
  · exact MergedCutProfiles.Batch534.valid21380
  · exact MergedCutProfiles.Batch534.valid21381
  · exact MergedCutProfiles.Batch534.valid21382
  · exact MergedCutProfiles.Batch534.valid21383
  · exact MergedCutProfiles.Batch534.valid21384
  · exact MergedCutProfiles.Batch534.valid21385
  · exact MergedCutProfiles.Batch534.valid21386
  · exact MergedCutProfiles.Batch534.valid21387
  · exact MergedCutProfiles.Batch534.valid21388
  · exact MergedCutProfiles.Batch534.valid21389
  · exact MergedCutProfiles.Batch534.valid21390
  · exact MergedCutProfiles.Batch534.valid21391
  · exact MergedCutProfiles.Batch534.valid21392
theorem numericValid3481 : retention3481.NumericValid := by decide +kernel
def certificate3481 : RatCutBinCertificate := ⟨⟨retention3481,(70023092426178137/31250000000000000),(50258241146397749/250000000000000000),(16542216660907816767/1000000000000000000),(938727443778951818319/1000000000000000000),(2135422110940865399/1000000000000000000)⟩,(499043685709745071/500000000000000000),(19691780175554649/62500000000000000),(40127880236763287/125000000000000000),(184452437108929931/1000000000000000000)⟩
theorem valid3481 : certificate3481.Valid := by decide +kernel
theorem sound3481 : certificate3481.Sound := rat_cut_bin_certificate_sound certificate3481 profilesValid3481 numericValid3481 valid3481

def retention3482 : RatCutRetentionCertificate := ⟨(249/4000),(1/16),(1098858119000000000/56659250567406957463),(66787883191014039/62500000000000000),(5/2),(2189444831400970863/1000000000000000000),true,MergedCutProfiles.Batch534.profile21393,![MergedCutProfiles.Batch534.profile21393,MergedCutProfiles.Batch534.profile21394,MergedCutProfiles.Batch534.profile21395,MergedCutProfiles.Batch534.profile21396,MergedCutProfiles.Batch534.profile21366,MergedCutProfiles.Batch534.profile21397,MergedCutProfiles.Batch534.profile21398,MergedCutProfiles.Batch534.profile21399,MergedCutProfiles.Batch535.profile21400,MergedCutProfiles.Batch535.profile21401,MergedCutProfiles.Batch535.profile21402,MergedCutProfiles.Batch535.profile21403,MergedCutProfiles.Batch535.profile21404,MergedCutProfiles.Batch535.profile21405,MergedCutProfiles.Batch535.profile21406,MergedCutProfiles.Batch535.profile21407]⟩
theorem profilesValid3482 : retention3482.ProfilesValid := by
  change ∀ j : Fin 16, (retention3482.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch534.valid21393
  · exact MergedCutProfiles.Batch534.valid21394
  · exact MergedCutProfiles.Batch534.valid21395
  · exact MergedCutProfiles.Batch534.valid21396
  · exact MergedCutProfiles.Batch534.valid21366
  · exact MergedCutProfiles.Batch534.valid21397
  · exact MergedCutProfiles.Batch534.valid21398
  · exact MergedCutProfiles.Batch534.valid21399
  · exact MergedCutProfiles.Batch535.valid21400
  · exact MergedCutProfiles.Batch535.valid21401
  · exact MergedCutProfiles.Batch535.valid21402
  · exact MergedCutProfiles.Batch535.valid21403
  · exact MergedCutProfiles.Batch535.valid21404
  · exact MergedCutProfiles.Batch535.valid21405
  · exact MergedCutProfiles.Batch535.valid21406
  · exact MergedCutProfiles.Batch535.valid21407
theorem numericValid3482 : retention3482.NumericValid := by decide +kernel
def certificate3482 : RatCutBinCertificate := ⟨⟨retention3482,(70023092426178137/31250000000000000),(50258241146397749/250000000000000000),(16542216660907816767/1000000000000000000),(938727443778951818319/1000000000000000000),(530340419658498631/250000000000000000)⟩,(499043685709745071/500000000000000000),(295923641109869571/1000000000000000000),(343718150338073037/1000000000000000000),(220848913240348033/1000000000000000000)⟩
theorem valid3482 : certificate3482.Valid := by decide +kernel
theorem sound3482 : certificate3482.Sound := rat_cut_bin_certificate_sound certificate3482 profilesValid3482 numericValid3482 valid3482

def retention3483 : RatCutRetentionCertificate := ⟨(249/4000),(1/16),(1192210035471918716/56659250567406957463),(1098858119/1000000000),(49/20),(4364716955098070363/2000000000000000000),true,MergedCutProfiles.Batch535.profile21408,![MergedCutProfiles.Batch535.profile21408,MergedCutProfiles.Batch535.profile21409,MergedCutProfiles.Batch535.profile21410,MergedCutProfiles.Batch535.profile21411,MergedCutProfiles.Batch535.profile21412,MergedCutProfiles.Batch535.profile21413,MergedCutProfiles.Batch535.profile21414,MergedCutProfiles.Batch534.profile21385,MergedCutProfiles.Batch534.profile21386,MergedCutProfiles.Batch534.profile21373,MergedCutProfiles.Batch535.profile21403,MergedCutProfiles.Batch535.profile21404,MergedCutProfiles.Batch535.profile21415,MergedCutProfiles.Batch535.profile21416,MergedCutProfiles.Batch535.profile21417,MergedCutProfiles.Batch535.profile21418]⟩
theorem profilesValid3483 : retention3483.ProfilesValid := by
  change ∀ j : Fin 16, (retention3483.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch535.valid21408
  · exact MergedCutProfiles.Batch535.valid21409
  · exact MergedCutProfiles.Batch535.valid21410
  · exact MergedCutProfiles.Batch535.valid21411
  · exact MergedCutProfiles.Batch535.valid21412
  · exact MergedCutProfiles.Batch535.valid21413
  · exact MergedCutProfiles.Batch535.valid21414
  · exact MergedCutProfiles.Batch534.valid21385
  · exact MergedCutProfiles.Batch534.valid21386
  · exact MergedCutProfiles.Batch534.valid21373
  · exact MergedCutProfiles.Batch535.valid21403
  · exact MergedCutProfiles.Batch535.valid21404
  · exact MergedCutProfiles.Batch535.valid21415
  · exact MergedCutProfiles.Batch535.valid21416
  · exact MergedCutProfiles.Batch535.valid21417
  · exact MergedCutProfiles.Batch535.valid21418
theorem numericValid3483 : retention3483.NumericValid := by decide +kernel
def certificate3483 : RatCutBinCertificate := ⟨⟨retention3483,(70023092426178137/31250000000000000),(50258241146397749/250000000000000000),(16542216660907816767/1000000000000000000),(938727443778951818319/1000000000000000000),(423127405786539847/200000000000000000)⟩,(499043685709745071/500000000000000000),(29332802173597499/100000000000000000),(346888298615516609/1000000000000000000),(56571281234715603/250000000000000000)⟩
theorem valid3483 : certificate3483.Valid := by decide +kernel
theorem sound3483 : certificate3483.Sound := rat_cut_bin_certificate_sound certificate3483 profilesValid3483 numericValid3483 valid3483

def retention3484 : RatCutRetentionCertificate := ⟨(249/4000),(1/16),(2669218028999529969/56659250567406957463),(298052508867979679/250000000000000000),(47/20),(167406518679366116121/80000000000000000000),true,MergedCutProfiles.Batch535.profile21419,![MergedCutProfiles.Batch535.profile21419,MergedCutProfiles.Batch534.profile21381,MergedCutProfiles.Batch535.profile21420,MergedCutProfiles.Batch534.profile21386,MergedCutProfiles.Batch535.profile21421,MergedCutProfiles.Batch534.profile21391,MergedCutProfiles.Batch535.profile21422,MergedCutProfiles.Batch535.profile21423,MergedCutProfiles.Batch535.profile21424,MergedCutProfiles.Batch535.profile21425,MergedCutProfiles.Batch535.profile21426,MergedCutProfiles.Batch535.profile21427,MergedCutProfiles.Batch535.profile21428,MergedCutProfiles.Batch535.profile21429,MergedCutProfiles.Batch535.profile21430,MergedCutProfiles.Batch535.profile21431]⟩
theorem profilesValid3484 : retention3484.ProfilesValid := by
  change ∀ j : Fin 16, (retention3484.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch535.valid21419
  · exact MergedCutProfiles.Batch534.valid21381
  · exact MergedCutProfiles.Batch535.valid21420
  · exact MergedCutProfiles.Batch534.valid21386
  · exact MergedCutProfiles.Batch535.valid21421
  · exact MergedCutProfiles.Batch534.valid21391
  · exact MergedCutProfiles.Batch535.valid21422
  · exact MergedCutProfiles.Batch535.valid21423
  · exact MergedCutProfiles.Batch535.valid21424
  · exact MergedCutProfiles.Batch535.valid21425
  · exact MergedCutProfiles.Batch535.valid21426
  · exact MergedCutProfiles.Batch535.valid21427
  · exact MergedCutProfiles.Batch535.valid21428
  · exact MergedCutProfiles.Batch535.valid21429
  · exact MergedCutProfiles.Batch535.valid21430
  · exact MergedCutProfiles.Batch535.valid21431
theorem numericValid3484 : retention3484.NumericValid := by decide +kernel
def certificate3484 : RatCutBinCertificate := ⟨⟨retention3484,(70023092426178137/31250000000000000),(50258241146397749/250000000000000000),(16542216660907816767/1000000000000000000),(938727443778951818319/1000000000000000000),(63393236195128399/31250000000000000)⟩,(499043685709745071/500000000000000000),(29611868638083773/100000000000000000),(343480849968102729/1000000000000000000),(56537990825042687/250000000000000000)⟩
theorem valid3484 : certificate3484.Valid := by decide +kernel
theorem sound3484 : certificate3484.Sound := rat_cut_bin_certificate_sound certificate3484 profilesValid3484 numericValid3484 valid3484

def retention3485 : RatCutRetentionCertificate := ⟨(249/4000),(1/16),(16653933478259455264/56659250567406957463),(2669218028999529969/1000000000000000000),(7/5),(94825021580833550068897997351330538179/66730450724988249225000000000000000000),false,MergedCutProfiles.Batch535.profile21432,(fun _ => MergedCutProfiles.Batch535.profile21432)⟩
theorem profilesValid3485 : retention3485.ProfilesValid := by
  exact MergedCutProfiles.Batch535.valid21432
theorem numericValid3485 : retention3485.NumericValid := by decide +kernel
def certificate3485 : RatCutBinCertificate := ⟨⟨retention3485,(70023092426178137/31250000000000000),(50258241146397749/250000000000000000),(16542216660907816767/1000000000000000000),(938727443778951818319/1000000000000000000),(138289005717295307/100000000000000000)⟩,(499043685709745071/500000000000000000),(340772249837213691/1000000000000000000),(292364942967373083/1000000000000000000),(227916113020176773/1000000000000000000)⟩
theorem valid3485 : certificate3485.Valid := by decide +kernel
theorem sound3485 : certificate3485.Sound := rat_cut_bin_certificate_sound certificate3485 profilesValid3485 numericValid3485 valid3485

def retention3486 : RatCutRetentionCertificate := ⟨(249/4000),(1/16),(3912798422459523554/8094178652486708209),(520435421195607977/31250000000000000),1,(4242009288924366087205508959945832223/4163483369564863816000000000000000000),false,MergedCutProfiles.Batch535.profile21433,(fun _ => MergedCutProfiles.Batch535.profile21433)⟩
theorem profilesValid3486 : retention3486.ProfilesValid := by
  exact MergedCutProfiles.Batch535.valid21433
theorem numericValid3486 : retention3486.NumericValid := by decide +kernel
def certificate3486 : RatCutBinCertificate := ⟨⟨retention3486,(70023092426178137/31250000000000000),(50258241146397749/250000000000000000),(16542216660907816767/1000000000000000000),(938727443778951818319/1000000000000000000),(495814600817415211/500000000000000000)⟩,(499043685709745071/500000000000000000),(386745027111751863/1000000000000000000),(61462299983212861/250000000000000000),(57408533303032577/250000000000000000)⟩
theorem valid3486 : certificate3486.Valid := by decide +kernel
theorem sound3486 : certificate3486.Sound := rat_cut_bin_certificate_sound certificate3486 profilesValid3486 numericValid3486 valid3486

def retention3487 : RatCutRetentionCertificate := ⟨(249/4000),(1/16),(28219520892209287042/56659250567406957463),(13694794478608332439/500000000000000000),1,(5457576061422387791637634029279894903/5477917791443332975600000000000000000),false,MergedCutProfiles.Batch535.profile21434,(fun _ => MergedCutProfiles.Batch535.profile21434)⟩
theorem profilesValid3487 : retention3487.ProfilesValid := by
  exact MergedCutProfiles.Batch535.valid21434
theorem numericValid3487 : retention3487.NumericValid := by decide +kernel
def certificate3487 : RatCutBinCertificate := ⟨⟨retention3487,(70023092426178137/31250000000000000),(50258241146397749/250000000000000000),(16542216660907816767/1000000000000000000),(938727443778951818319/1000000000000000000),(2422638258473867/2500000000000000)⟩,(499043685709745071/500000000000000000),(77796056947718539/200000000000000000),(243732304302780203/1000000000000000000),(227672535050536623/1000000000000000000)⟩
theorem valid3487 : certificate3487.Valid := by decide +kernel
theorem sound3487 : certificate3487.Sound := rat_cut_bin_certificate_sound certificate3487 profilesValid3487 numericValid3487 valid3487

def retention3488 : RatCutRetentionCertificate := ⟨(249/4000),(1/16),(1/2),(14109760446104643521/500000000000000000),1,(112057832377458211150581777301820504367/112878083568837148168000000000000000000),false,MergedCutProfiles.Batch535.profile21435,(fun _ => MergedCutProfiles.Batch535.profile21435)⟩
theorem profilesValid3488 : retention3488.ProfilesValid := by
  exact MergedCutProfiles.Batch535.valid21435
theorem numericValid3488 : retention3488.NumericValid := by decide +kernel
def certificate3488 : RatCutBinCertificate := ⟨⟨retention3488,(70023092426178137/31250000000000000),(50258241146397749/250000000000000000),(16542216660907816767/1000000000000000000),(938727443778951818319/1000000000000000000),(193100402990906789/200000000000000000)⟩,(499043685709745071/500000000000000000),(195050824807397537/500000000000000000),(242675158166332551/1000000000000000000),(226108867727034681/1000000000000000000)⟩
theorem valid3488 : certificate3488.Valid := by decide +kernel
theorem sound3488 : certificate3488.Sound := rat_cut_bin_certificate_sound certificate3488 profilesValid3488 numericValid3488 valid3488

def retention3489 : RatCutRetentionCertificate := ⟨(249/4000),(1/16),(26134213196016581858/56659250567406957463),(9012025976924021861/1000000000000000000),1,(7551156012185624824956244430867840591/7209620781539217488800000000000000000),false,MergedCutProfiles.Batch535.profile21436,(fun _ => MergedCutProfiles.Batch535.profile21436)⟩
theorem profilesValid3489 : retention3489.ProfilesValid := by
  exact MergedCutProfiles.Batch535.valid21436
theorem numericValid3489 : retention3489.NumericValid := by decide +kernel
def certificate3489 : RatCutBinCertificate := ⟨⟨retention3489,(71954379926178137/31250000000000000),(50258241146397749/250000000000000000),(16542216660907816767/1000000000000000000),(938727443778951818319/1000000000000000000),(101938935313837771/100000000000000000)⟩,(998034593965110883/1000000000000000000),(118131689807012961/1000000000000000000),(627377499726722839/1000000000000000000),(573349413431034547/1000000000000000000)⟩
theorem valid3489 : certificate3489.Valid := by decide +kernel
theorem sound3489 : certificate3489.Sound := rat_cut_bin_certificate_sound certificate3489 profilesValid3489 numericValid3489 valid3489

def retention3490 : RatCutRetentionCertificate := ⟨(249/4000),(1/16),(4002773409564415021/8094178652486708209),(13067106598008290929/500000000000000000),1,(20965685684273646007994003776644503043/20907370556813265486400000000000000000),false,MergedCutProfiles.Batch535.profile21437,(fun _ => MergedCutProfiles.Batch535.profile21437)⟩
theorem profilesValid3490 : retention3490.ProfilesValid := by
  exact MergedCutProfiles.Batch535.valid21437
theorem numericValid3490 : retention3490.NumericValid := by decide +kernel
def certificate3490 : RatCutBinCertificate := ⟨⟨retention3490,(71954379926178137/31250000000000000),(50258241146397749/250000000000000000),(16542216660907816767/1000000000000000000),(938727443778951818319/1000000000000000000),(38992274141180967/40000000000000000)⟩,(998034593965110883/1000000000000000000),(61767203637057307/500000000000000000),(616224686760526669/1000000000000000000),(577934130166348927/1000000000000000000)⟩
theorem valid3490 : certificate3490.Valid := by decide +kernel
theorem sound3490 : certificate3490.Sound := rat_cut_bin_certificate_sound certificate3490 profilesValid3490 numericValid3490 valid3490

def retention3491 : RatCutRetentionCertificate := ⟨(249/4000),(1/16),(28299608005620414199/56659250567406957463),(28019413866950905147/1000000000000000000),1,(3182083866365668049351007193209366881/3202218727651532016800000000000000000),false,MergedCutProfiles.Batch535.profile21438,(fun _ => MergedCutProfiles.Batch535.profile21438)⟩
theorem profilesValid3491 : retention3491.ProfilesValid := by
  exact MergedCutProfiles.Batch535.valid21438
theorem numericValid3491 : retention3491.NumericValid := by decide +kernel
def certificate3491 : RatCutBinCertificate := ⟨⟨retention3491,(71954379926178137/31250000000000000),(50258241146397749/250000000000000000),(16542216660907816767/1000000000000000000),(938727443778951818319/1000000000000000000),(193145974121747017/200000000000000000)⟩,(998034593965110883/1000000000000000000),(62347759203931371/500000000000000000),(76731823846228037/125000000000000000),(571914561757789979/1000000000000000000)⟩
theorem valid3491 : certificate3491.Valid := by decide +kernel
theorem sound3491 : certificate3491.Sound := rat_cut_bin_certificate_sound certificate3491 profilesValid3491 numericValid3491 valid3491

def certificates : List RatCutBinCertificate := [certificate3480,certificate3481,certificate3482,certificate3483,certificate3484,certificate3485,certificate3486,certificate3487,certificate3488,certificate3489,certificate3490,certificate3491]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound3480,List.forall_mem_cons.mpr ⟨sound3481,List.forall_mem_cons.mpr ⟨sound3482,List.forall_mem_cons.mpr ⟨sound3483,List.forall_mem_cons.mpr ⟨sound3484,List.forall_mem_cons.mpr ⟨sound3485,List.forall_mem_cons.mpr ⟨sound3486,List.forall_mem_cons.mpr ⟨sound3487,List.forall_mem_cons.mpr ⟨sound3488,List.forall_mem_cons.mpr ⟨sound3489,List.forall_mem_cons.mpr ⟨sound3490,List.forall_mem_cons.mpr ⟨sound3491,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch290
