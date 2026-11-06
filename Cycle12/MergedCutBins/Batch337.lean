import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch370
import Cycle12.MergedCutProfiles.Batch371
import Cycle12.MergedCutProfiles.Batch372
import Cycle12.MergedCutProfiles.Batch373
import Cycle12.MergedCutProfiles.Batch485
import Cycle12.MergedCutProfiles.Batch486
import Cycle12.MergedCutProfiles.Batch609
import Cycle12.MergedCutProfiles.Batch610

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch337

def retention4044 : RatCutRetentionCertificate := ⟨(47/1000),(6/125),(64000000000000000000/418748044271657088761),(24932302261032562341/1000000000000000000),1,(34616239284610636691748793348742787967/19945841808826049872800000000000000000),false,MergedCutProfiles.Batch609.profile24374,(fun _ => MergedCutProfiles.Batch609.profile24374)⟩
theorem profilesValid4044 : retention4044.ProfilesValid := by
  exact MergedCutProfiles.Batch609.valid24374
theorem numericValid4044 : retention4044.NumericValid := by decide +kernel
def certificate4044 : RatCutBinCertificate := ⟨⟨retention4044,(231922781356841151/125000000000000000),(13651068898300767/125000000000000000),(12679903510959588819/1000000000000000000),(5339694884310694289539/1000000000000000000),(1719531658126662559/1000000000000000000)⟩,(499844358539873217/500000000000000000),(8205088652159407/250000000000000000),(418048099548570163/500000000000000000),(67225357286478271/50000000000000000)⟩
theorem valid4044 : certificate4044.Valid := by decide +kernel
theorem sound4044 : certificate4044.Sound := rat_cut_bin_certificate_sound certificate4044 profilesValid4044 numericValid4044 valid4044

def retention4045 : RatCutRetentionCertificate := ⟨(47/1000),(6/125),(1/2),64,1,(15961943206562927268838532628520865151/16000000000000000000000000000000000000),false,MergedCutProfiles.Batch370.profile14826,(fun _ => MergedCutProfiles.Batch370.profile14826)⟩
theorem profilesValid4045 : retention4045.ProfilesValid := by
  exact MergedCutProfiles.Batch370.valid14826
theorem numericValid4045 : retention4045.NumericValid := by decide +kernel
def certificate4045 : RatCutBinCertificate := ⟨⟨retention4045,(231922781356841151/125000000000000000),(13651068898300767/125000000000000000),(12679903510959588819/1000000000000000000),(5339694884310694289539/1000000000000000000),(245410385982864633/250000000000000000)⟩,(499844358539873217/500000000000000000),(14372771590959743/250000000000000000),(768569966880462501/1000000000000000000),(46426832482909981/62500000000000000)⟩
theorem valid4045 : certificate4045.Valid := by decide +kernel
theorem sound4045 : certificate4045.Sound := rat_cut_bin_certificate_sound certificate4045 profilesValid4045 numericValid4045 valid4045

def retention4046 : RatCutRetentionCertificate := ⟨(6/125),(49/1000),(212203324887811763/133185969655715456751),(78788363200920209/125000000000000000),4,(5837037302423744206878207829648600119/2521227622429446688000000000000000000),true,MergedCutProfiles.Batch609.profile24375,![MergedCutProfiles.Batch609.profile24375,MergedCutProfiles.Batch609.profile24376,MergedCutProfiles.Batch609.profile24377,MergedCutProfiles.Batch609.profile24378,MergedCutProfiles.Batch485.profile19427,MergedCutProfiles.Batch485.profile19437,MergedCutProfiles.Batch486.profile19452,MergedCutProfiles.Batch609.profile24379,MergedCutProfiles.Batch609.profile24380,MergedCutProfiles.Batch609.profile24381,MergedCutProfiles.Batch609.profile24382,MergedCutProfiles.Batch609.profile24383,MergedCutProfiles.Batch370.profile14829,MergedCutProfiles.Batch486.profile19453,MergedCutProfiles.Batch609.profile24384,MergedCutProfiles.Batch371.profile14860]⟩
theorem profilesValid4046 : retention4046.ProfilesValid := by
  change ∀ j : Fin 16, (retention4046.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch609.valid24375
  · exact MergedCutProfiles.Batch609.valid24376
  · exact MergedCutProfiles.Batch609.valid24377
  · exact MergedCutProfiles.Batch609.valid24378
  · exact MergedCutProfiles.Batch485.valid19427
  · exact MergedCutProfiles.Batch485.valid19437
  · exact MergedCutProfiles.Batch486.valid19452
  · exact MergedCutProfiles.Batch609.valid24379
  · exact MergedCutProfiles.Batch609.valid24380
  · exact MergedCutProfiles.Batch609.valid24381
  · exact MergedCutProfiles.Batch609.valid24382
  · exact MergedCutProfiles.Batch609.valid24383
  · exact MergedCutProfiles.Batch370.valid14829
  · exact MergedCutProfiles.Batch486.valid19453
  · exact MergedCutProfiles.Batch609.valid24384
  · exact MergedCutProfiles.Batch371.valid14860
theorem numericValid4046 : retention4046.NumericValid := by decide +kernel
def certificate4046 : RatCutBinCertificate := ⟨⟨retention4046,(1934473188126154257/1000000000000000000),(114392751307786871/1000000000000000000),(12888805750199486359/1000000000000000000),(5179117747129619376949/1000000000000000000),(17971837195816613/8000000000000000)⟩,(999667263295824949/1000000000000000000),(636639087904011001/1000000000000000000),(75885026134257517/1000000000000000000),(34840449175861863/1000000000000000000)⟩
theorem valid4046 : certificate4046.Valid := by decide +kernel
theorem sound4046 : certificate4046.Sound := rat_cut_bin_certificate_sound certificate4046 profilesValid4046 numericValid4046 valid4046

def retention4047 : RatCutRetentionCertificate := ⟨(6/125),(49/1000),(1109286628000000000/399557908967146370253),(636609974663435289/1000000000000000000),4,(147975353243268319049/64000000000000000000),true,MergedCutProfiles.Batch609.profile24385,![MergedCutProfiles.Batch609.profile24385,MergedCutProfiles.Batch609.profile24386,MergedCutProfiles.Batch609.profile24387,MergedCutProfiles.Batch609.profile24388,MergedCutProfiles.Batch609.profile24389,MergedCutProfiles.Batch609.profile24390,MergedCutProfiles.Batch485.profile19438,MergedCutProfiles.Batch486.profile19453,MergedCutProfiles.Batch609.profile24391,MergedCutProfiles.Batch609.profile24392,MergedCutProfiles.Batch609.profile24393,MergedCutProfiles.Batch486.profile19454,MergedCutProfiles.Batch609.profile24394,MergedCutProfiles.Batch485.profile19430,MergedCutProfiles.Batch370.profile14830,MergedCutProfiles.Batch486.profile19466]⟩
theorem profilesValid4047 : retention4047.ProfilesValid := by
  change ∀ j : Fin 16, (retention4047.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch609.valid24385
  · exact MergedCutProfiles.Batch609.valid24386
  · exact MergedCutProfiles.Batch609.valid24387
  · exact MergedCutProfiles.Batch609.valid24388
  · exact MergedCutProfiles.Batch609.valid24389
  · exact MergedCutProfiles.Batch609.valid24390
  · exact MergedCutProfiles.Batch485.valid19438
  · exact MergedCutProfiles.Batch486.valid19453
  · exact MergedCutProfiles.Batch609.valid24391
  · exact MergedCutProfiles.Batch609.valid24392
  · exact MergedCutProfiles.Batch609.valid24393
  · exact MergedCutProfiles.Batch486.valid19454
  · exact MergedCutProfiles.Batch609.valid24394
  · exact MergedCutProfiles.Batch485.valid19430
  · exact MergedCutProfiles.Batch370.valid14830
  · exact MergedCutProfiles.Batch486.valid19466
theorem numericValid4047 : retention4047.NumericValid := by decide +kernel
def certificate4047 : RatCutBinCertificate := ⟨⟨retention4047,(1934473188126154257/1000000000000000000),(114392751307786871/1000000000000000000),(12888805750199486359/1000000000000000000),(5179117747129619376949/1000000000000000000),(2243437738750986003/1000000000000000000)⟩,(999667263295824949/1000000000000000000),(39592733701027877/62500000000000000),(19329415895224193/250000000000000000),(4440363172945447/125000000000000000)⟩
theorem valid4047 : certificate4047.Valid := by decide +kernel
theorem sound4047 : certificate4047.Sound := rat_cut_bin_certificate_sound certificate4047 profilesValid4047 numericValid4047 valid4047

def retention4048 : RatCutRetentionCertificate := ⟨(6/125),(49/1000),(1654723071283712618/399557908967146370253),(277321657/250000000),(14/5),(2348475201875454323/1000000000000000000),true,MergedCutProfiles.Batch609.profile24395,![MergedCutProfiles.Batch609.profile24395,MergedCutProfiles.Batch609.profile24387,MergedCutProfiles.Batch609.profile24379,MergedCutProfiles.Batch609.profile24396,MergedCutProfiles.Batch370.profile14829,MergedCutProfiles.Batch609.profile24391,MergedCutProfiles.Batch486.profile19465,MergedCutProfiles.Batch486.profile19454,MergedCutProfiles.Batch609.profile24397,MergedCutProfiles.Batch370.profile14830,MergedCutProfiles.Batch609.profile24398,MergedCutProfiles.Batch371.profile14861,MergedCutProfiles.Batch372.profile14887,MergedCutProfiles.Batch609.profile24399,MergedCutProfiles.Batch485.profile19431,MergedCutProfiles.Batch610.profile24400]⟩
theorem profilesValid4048 : retention4048.ProfilesValid := by
  change ∀ j : Fin 16, (retention4048.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch609.valid24395
  · exact MergedCutProfiles.Batch609.valid24387
  · exact MergedCutProfiles.Batch609.valid24379
  · exact MergedCutProfiles.Batch609.valid24396
  · exact MergedCutProfiles.Batch370.valid14829
  · exact MergedCutProfiles.Batch609.valid24391
  · exact MergedCutProfiles.Batch486.valid19465
  · exact MergedCutProfiles.Batch486.valid19454
  · exact MergedCutProfiles.Batch609.valid24397
  · exact MergedCutProfiles.Batch370.valid14830
  · exact MergedCutProfiles.Batch609.valid24398
  · exact MergedCutProfiles.Batch371.valid14861
  · exact MergedCutProfiles.Batch372.valid14887
  · exact MergedCutProfiles.Batch609.valid24399
  · exact MergedCutProfiles.Batch485.valid19431
  · exact MergedCutProfiles.Batch610.valid24400
theorem numericValid4048 : retention4048.NumericValid := by decide +kernel
def certificate4048 : RatCutBinCertificate := ⟨⟨retention4048,(1934473188126154257/1000000000000000000),(114392751307786871/1000000000000000000),(12888805750199486359/1000000000000000000),(5179117747129619376949/1000000000000000000),(287550158503017857/125000000000000000)⟩,(999667263295824949/1000000000000000000),(450802280767043799/1000000000000000000),(190031352356238497/1000000000000000000),(123418391284187031/1000000000000000000)⟩
theorem valid4048 : certificate4048.Valid := by decide +kernel
theorem sound4048 : certificate4048.Sound := rat_cut_bin_certificate_sound certificate4048 profilesValid4048 numericValid4048 valid4048

def retention4049 : RatCutRetentionCertificate := ⟨(6/125),(49/1000),(44134546708153886531/399557908967146370253),(827361535641856309/500000000000000000),(21/10),(78019141829562745123585913893845157481/41368076782092815450000000000000000000),false,MergedCutProfiles.Batch610.profile24401,(fun _ => MergedCutProfiles.Batch610.profile24401)⟩
theorem profilesValid4049 : retention4049.ProfilesValid := by
  exact MergedCutProfiles.Batch610.valid24401
theorem numericValid4049 : retention4049.NumericValid := by decide +kernel
def certificate4049 : RatCutBinCertificate := ⟨⟨retention4049,(1934473188126154257/1000000000000000000),(114392751307786871/1000000000000000000),(12888805750199486359/1000000000000000000),(5179117747129619376949/1000000000000000000),(924959585607973663/500000000000000000)⟩,(999667263295824949/1000000000000000000),(117097383164158233/250000000000000000),(176357935390290451/1000000000000000000),(123889909908242979/1000000000000000000)⟩
theorem valid4049 : certificate4049.Valid := by decide +kernel
theorem sound4049 : certificate4049.Sound := rat_cut_bin_certificate_sound certificate4049 profilesValid4049 numericValid4049 valid4049

def retention4050 : RatCutRetentionCertificate := ⟨(6/125),(49/1000),(64000000000000000000/399557908967146370253),(44134546708153886531/1000000000000000000),1,(61107911931586779029848577236371327639/35307637366523109224800000000000000000),false,MergedCutProfiles.Batch610.profile24402,(fun _ => MergedCutProfiles.Batch610.profile24402)⟩
theorem profilesValid4050 : retention4050.ProfilesValid := by
  exact MergedCutProfiles.Batch610.valid24402
theorem numericValid4050 : retention4050.NumericValid := by decide +kernel
def certificate4050 : RatCutBinCertificate := ⟨⟨retention4050,(1934473188126154257/1000000000000000000),(114392751307786871/1000000000000000000),(12888805750199486359/1000000000000000000),(5179117747129619376949/1000000000000000000),(68542348762947131/40000000000000000)⟩,(999667263295824949/1000000000000000000),(38855007267250659/125000000000000000),(325933364401898717/1000000000000000000),(537450558490714361/1000000000000000000)⟩
theorem valid4050 : certificate4050.Valid := by decide +kernel
theorem sound4050 : certificate4050.Sound := rat_cut_bin_certificate_sound certificate4050 profilesValid4050 numericValid4050 valid4050

def retention4051 : RatCutRetentionCertificate := ⟨(6/125),(49/1000),(1/2),64,1,(9976258213095706455955121867646831/10000000000000000000000000000000000),false,MergedCutProfiles.Batch372.profile14918,(fun _ => MergedCutProfiles.Batch372.profile14918)⟩
theorem profilesValid4051 : retention4051.ProfilesValid := by
  exact MergedCutProfiles.Batch372.valid14918
theorem numericValid4051 : retention4051.NumericValid := by decide +kernel
def certificate4051 : RatCutBinCertificate := ⟨⟨retention4051,(1934473188126154257/1000000000000000000),(114392751307786871/1000000000000000000),(12888805750199486359/1000000000000000000),(5179117747129619376949/1000000000000000000),(24511416884678373/25000000000000000)⟩,(999667263295824949/1000000000000000000),(269571443024139551/500000000000000000),(25557659023012399/200000000000000000),(123358968799590879/1000000000000000000)⟩
theorem valid4051 : certificate4051.Valid := by decide +kernel
theorem sound4051 : certificate4051.Sound := rat_cut_bin_certificate_sound certificate4051 profilesValid4051 numericValid4051 valid4051

def retention4052 : RatCutRetentionCertificate := ⟨(6/125),(49/1000),(64000000000000000000/399557908967146370253),(25086596723691509049/1000000000000000000),1,(57451171223644117900644280643860461321/33448795631588678732000000000000000000),false,MergedCutProfiles.Batch610.profile24402,(fun _ => MergedCutProfiles.Batch610.profile24402)⟩
theorem profilesValid4052 : retention4052.ProfilesValid := by
  exact MergedCutProfiles.Batch610.valid24402
theorem numericValid4052 : retention4052.NumericValid := by decide +kernel
def certificate4052 : RatCutBinCertificate := ⟨⟨retention4052,(1858279946126154257/1000000000000000000),(114392751307786871/1000000000000000000),(12888805750199486359/1000000000000000000),(5179117747129619376949/1000000000000000000),(850546366413850823/500000000000000000)⟩,(499840184667574111/500000000000000000),(6567630206729767/200000000000000000),(836044992005413079/1000000000000000000),(1331440632108447149/1000000000000000000)⟩
theorem valid4052 : certificate4052.Valid := by decide +kernel
theorem sound4052 : certificate4052.Sound := rat_cut_bin_certificate_sound certificate4052 profilesValid4052 numericValid4052 valid4052

def retention4053 : RatCutRetentionCertificate := ⟨(6/125),(49/1000),(1/2),64,1,(9976258213095706455955121867646831/10000000000000000000000000000000000),false,MergedCutProfiles.Batch372.profile14918,(fun _ => MergedCutProfiles.Batch372.profile14918)⟩
theorem profilesValid4053 : retention4053.ProfilesValid := by
  exact MergedCutProfiles.Batch372.valid14918
theorem numericValid4053 : retention4053.NumericValid := by decide +kernel
def certificate4053 : RatCutBinCertificate := ⟨⟨retention4053,(1858279946126154257/1000000000000000000),(114392751307786871/1000000000000000000),(12888805750199486359/1000000000000000000),(5179117747129619376949/1000000000000000000),(196226583567634143/200000000000000000)⟩,(499840184667574111/500000000000000000),(56934936202040927/1000000000000000000),(770019737140716491/1000000000000000000),(743844446127956033/1000000000000000000)⟩
theorem valid4053 : certificate4053.Valid := by decide +kernel
theorem sound4053 : certificate4053.Sound := rat_cut_bin_certificate_sound certificate4053 profilesValid4053 numericValid4053 valid4053

def retention4054 : RatCutRetentionCertificate := ⟨(49/1000),(1/20),(322143490525996416/190775530142471967995),(637907902031676071/1000000000000000000),4,(148810084088997149271/64000000000000000000),true,MergedCutProfiles.Batch610.profile24403,![MergedCutProfiles.Batch610.profile24403,MergedCutProfiles.Batch610.profile24404,MergedCutProfiles.Batch610.profile24405,MergedCutProfiles.Batch610.profile24406,MergedCutProfiles.Batch610.profile24407,MergedCutProfiles.Batch610.profile24408,MergedCutProfiles.Batch610.profile24409,MergedCutProfiles.Batch610.profile24410,MergedCutProfiles.Batch610.profile24411,MergedCutProfiles.Batch610.profile24412,MergedCutProfiles.Batch610.profile24413,MergedCutProfiles.Batch610.profile24414,MergedCutProfiles.Batch373.profile14921,MergedCutProfiles.Batch610.profile24415,MergedCutProfiles.Batch610.profile24416,MergedCutProfiles.Batch610.profile24417]⟩
theorem profilesValid4054 : retention4054.ProfilesValid := by
  change ∀ j : Fin 16, (retention4054.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch610.valid24403
  · exact MergedCutProfiles.Batch610.valid24404
  · exact MergedCutProfiles.Batch610.valid24405
  · exact MergedCutProfiles.Batch610.valid24406
  · exact MergedCutProfiles.Batch610.valid24407
  · exact MergedCutProfiles.Batch610.valid24408
  · exact MergedCutProfiles.Batch610.valid24409
  · exact MergedCutProfiles.Batch610.valid24410
  · exact MergedCutProfiles.Batch610.valid24411
  · exact MergedCutProfiles.Batch610.valid24412
  · exact MergedCutProfiles.Batch610.valid24413
  · exact MergedCutProfiles.Batch610.valid24414
  · exact MergedCutProfiles.Batch373.valid14921
  · exact MergedCutProfiles.Batch610.valid24415
  · exact MergedCutProfiles.Batch610.valid24416
  · exact MergedCutProfiles.Batch610.valid24417
theorem numericValid4054 : retention4054.NumericValid := by decide +kernel
def certificate4054 : RatCutBinCertificate := ⟨⟨retention4054,(485887555299514563/250000000000000000),(59865971199444307/500000000000000000),(3275756374603509871/250000000000000000),(5028094937505649710709/1000000000000000000),(1127059166290914121/500000000000000000)⟩,(199931532780840767/200000000000000000),(15602575549528147/25000000000000000),(81669958279134591/1000000000000000000),(37682243177418763/1000000000000000000)⟩
theorem valid4054 : certificate4054.Valid := by decide +kernel
theorem sound4054 : certificate4054.Sound := rat_cut_bin_certificate_sound certificate4054 profilesValid4054 numericValid4054 valid4054

def retention4055 : RatCutRetentionCertificate := ⟨(49/1000),(1/20),(109703224500000000/38155106028494393599),(2516746019734347/3906250000000000),4,(37149490809235262703/16000000000000000000),true,MergedCutProfiles.Batch610.profile24418,![MergedCutProfiles.Batch610.profile24418,MergedCutProfiles.Batch610.profile24419,MergedCutProfiles.Batch610.profile24407,MergedCutProfiles.Batch610.profile24420,MergedCutProfiles.Batch610.profile24421,MergedCutProfiles.Batch610.profile24422,MergedCutProfiles.Batch610.profile24414,MergedCutProfiles.Batch610.profile24423,MergedCutProfiles.Batch610.profile24424,MergedCutProfiles.Batch610.profile24425,MergedCutProfiles.Batch610.profile24426,MergedCutProfiles.Batch610.profile24427,MergedCutProfiles.Batch610.profile24428,MergedCutProfiles.Batch610.profile24429,MergedCutProfiles.Batch610.profile24430,MergedCutProfiles.Batch610.profile24431]⟩
theorem profilesValid4055 : retention4055.ProfilesValid := by
  change ∀ j : Fin 16, (retention4055.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch610.valid24418
  · exact MergedCutProfiles.Batch610.valid24419
  · exact MergedCutProfiles.Batch610.valid24407
  · exact MergedCutProfiles.Batch610.valid24420
  · exact MergedCutProfiles.Batch610.valid24421
  · exact MergedCutProfiles.Batch610.valid24422
  · exact MergedCutProfiles.Batch610.valid24414
  · exact MergedCutProfiles.Batch610.valid24423
  · exact MergedCutProfiles.Batch610.valid24424
  · exact MergedCutProfiles.Batch610.valid24425
  · exact MergedCutProfiles.Batch610.valid24426
  · exact MergedCutProfiles.Batch610.valid24427
  · exact MergedCutProfiles.Batch610.valid24428
  · exact MergedCutProfiles.Batch610.valid24429
  · exact MergedCutProfiles.Batch610.valid24430
  · exact MergedCutProfiles.Batch610.valid24431
theorem numericValid4055 : retention4055.NumericValid := by decide +kernel
def certificate4055 : RatCutBinCertificate := ⟨⟨retention4055,(485887555299514563/250000000000000000),(59865971199444307/500000000000000000),(3275756374603509871/250000000000000000),(5028094937505649710709/1000000000000000000),(1125401975416171743/500000000000000000)⟩,(199931532780840767/200000000000000000),(621108507693971457/1000000000000000000),(2596527720048023/31250000000000000),(1917969555099219/50000000000000000)⟩
theorem valid4055 : certificate4055.Valid := by decide +kernel
theorem sound4055 : certificate4055.Sound := rat_cut_bin_certificate_sound certificate4055 profilesValid4055 numericValid4055 valid4055

def certificates : List RatCutBinCertificate := [certificate4044,certificate4045,certificate4046,certificate4047,certificate4048,certificate4049,certificate4050,certificate4051,certificate4052,certificate4053,certificate4054,certificate4055]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound4044,List.forall_mem_cons.mpr ⟨sound4045,List.forall_mem_cons.mpr ⟨sound4046,List.forall_mem_cons.mpr ⟨sound4047,List.forall_mem_cons.mpr ⟨sound4048,List.forall_mem_cons.mpr ⟨sound4049,List.forall_mem_cons.mpr ⟨sound4050,List.forall_mem_cons.mpr ⟨sound4051,List.forall_mem_cons.mpr ⟨sound4052,List.forall_mem_cons.mpr ⟨sound4053,List.forall_mem_cons.mpr ⟨sound4054,List.forall_mem_cons.mpr ⟨sound4055,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch337
