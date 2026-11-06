import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch159
import Cycle12.MergedCutProfiles.Batch160
import Cycle12.MergedCutProfiles.Batch161

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch079

def retention948 : RatCutRetentionCertificate := ⟨(203/4000),(51/1000),(282033904792552669/6077232277014350716),(8294301680008411/10000000000000000),(59/20),(132488702182281986003/64000000000000000000),true,MergedCutProfiles.Batch159.profile6367,![MergedCutProfiles.Batch159.profile6367,MergedCutProfiles.Batch159.profile6368,MergedCutProfiles.Batch159.profile6369,MergedCutProfiles.Batch159.profile6370,MergedCutProfiles.Batch159.profile6371,MergedCutProfiles.Batch159.profile6372,MergedCutProfiles.Batch159.profile6373,MergedCutProfiles.Batch159.profile6374,MergedCutProfiles.Batch159.profile6375,MergedCutProfiles.Batch159.profile6376,MergedCutProfiles.Batch159.profile6377,MergedCutProfiles.Batch159.profile6378,MergedCutProfiles.Batch159.profile6379,MergedCutProfiles.Batch159.profile6380,MergedCutProfiles.Batch159.profile6381,MergedCutProfiles.Batch159.profile6382]⟩
theorem profilesValid948 : retention948.ProfilesValid := by
  change ∀ j : Fin 16, (retention948.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch159.valid6367
  · exact MergedCutProfiles.Batch159.valid6368
  · exact MergedCutProfiles.Batch159.valid6369
  · exact MergedCutProfiles.Batch159.valid6370
  · exact MergedCutProfiles.Batch159.valid6371
  · exact MergedCutProfiles.Batch159.valid6372
  · exact MergedCutProfiles.Batch159.valid6373
  · exact MergedCutProfiles.Batch159.valid6374
  · exact MergedCutProfiles.Batch159.valid6375
  · exact MergedCutProfiles.Batch159.valid6376
  · exact MergedCutProfiles.Batch159.valid6377
  · exact MergedCutProfiles.Batch159.valid6378
  · exact MergedCutProfiles.Batch159.valid6379
  · exact MergedCutProfiles.Batch159.valid6380
  · exact MergedCutProfiles.Batch159.valid6381
  · exact MergedCutProfiles.Batch159.valid6382
theorem numericValid948 : retention948.NumericValid := by decide +kernel
def certificate948 : RatCutBinCertificate := ⟨⟨retention948,(213756841287465781/100000000000000000),(31307344283847009/250000000000000000),(13488262449249347437/1000000000000000000),(246268246515930295277/1000000000000000000),(1005789237658704709/500000000000000000)⟩,(124048331567006351/125000000000000000),(120000937173099/312500000000000),(124231836107330559/500000000000000000),(5251909207209711/40000000000000000)⟩
theorem valid948 : certificate948.Valid := by decide +kernel
theorem sound948 : certificate948.Sound := rat_cut_bin_certificate_sound certificate948 profilesValid948 numericValid948 valid948

def retention949 : RatCutRetentionCertificate := ⟨(203/4000),(51/1000),(982297823477794495/18231696831043052148),(846101714377658007/1000000000000000000),(29/10),(2618287718994452251667/1280000000000000000000),true,MergedCutProfiles.Batch159.profile6383,![MergedCutProfiles.Batch159.profile6383,MergedCutProfiles.Batch159.profile6384,MergedCutProfiles.Batch159.profile6385,MergedCutProfiles.Batch159.profile6386,MergedCutProfiles.Batch159.profile6387,MergedCutProfiles.Batch159.profile6373,MergedCutProfiles.Batch159.profile6388,MergedCutProfiles.Batch159.profile6389,MergedCutProfiles.Batch159.profile6390,MergedCutProfiles.Batch159.profile6391,MergedCutProfiles.Batch159.profile6392,MergedCutProfiles.Batch159.profile6393,MergedCutProfiles.Batch159.profile6394,MergedCutProfiles.Batch159.profile6395,MergedCutProfiles.Batch159.profile6396,MergedCutProfiles.Batch159.profile6397]⟩
theorem profilesValid949 : retention949.ProfilesValid := by
  change ∀ j : Fin 16, (retention949.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch159.valid6383
  · exact MergedCutProfiles.Batch159.valid6384
  · exact MergedCutProfiles.Batch159.valid6385
  · exact MergedCutProfiles.Batch159.valid6386
  · exact MergedCutProfiles.Batch159.valid6387
  · exact MergedCutProfiles.Batch159.valid6373
  · exact MergedCutProfiles.Batch159.valid6388
  · exact MergedCutProfiles.Batch159.valid6389
  · exact MergedCutProfiles.Batch159.valid6390
  · exact MergedCutProfiles.Batch159.valid6391
  · exact MergedCutProfiles.Batch159.valid6392
  · exact MergedCutProfiles.Batch159.valid6393
  · exact MergedCutProfiles.Batch159.valid6394
  · exact MergedCutProfiles.Batch159.valid6395
  · exact MergedCutProfiles.Batch159.valid6396
  · exact MergedCutProfiles.Batch159.valid6397
theorem numericValid949 : retention949.NumericValid := by decide +kernel
def certificate949 : RatCutBinCertificate := ⟨⟨retention949,(213756841287465781/100000000000000000),(31307344283847009/250000000000000000),(13488262449249347437/1000000000000000000),(246268246515930295277/1000000000000000000),(62124134926206933/31250000000000000)⟩,(124048331567006351/125000000000000000),(9634711782343397/25000000000000000),(123570106781357803/500000000000000000),(2050321424916129/15625000000000000)⟩
theorem valid949 : certificate949.Valid := by decide +kernel
theorem sound949 : certificate949.Sound := rat_cut_bin_certificate_sound certificate949 profilesValid949 numericValid949 valid949

def retention950 : RatCutRetentionCertificate := ⟨(203/4000),(51/1000),(975861034163244041/9115848415521526074),(196459564695558899/200000000000000000),(51/20),(480968188374515708211/256000000000000000000),true,MergedCutProfiles.Batch159.profile6398,![MergedCutProfiles.Batch159.profile6398,MergedCutProfiles.Batch159.profile6399,MergedCutProfiles.Batch160.profile6400,MergedCutProfiles.Batch160.profile6401,MergedCutProfiles.Batch160.profile6402,MergedCutProfiles.Batch160.profile6403,MergedCutProfiles.Batch160.profile6404,MergedCutProfiles.Batch160.profile6405,MergedCutProfiles.Batch160.profile6406,MergedCutProfiles.Batch160.profile6407,MergedCutProfiles.Batch160.profile6408,MergedCutProfiles.Batch160.profile6409,MergedCutProfiles.Batch160.profile6410,MergedCutProfiles.Batch160.profile6411,MergedCutProfiles.Batch160.profile6412,MergedCutProfiles.Batch160.profile6413]⟩
theorem profilesValid950 : retention950.ProfilesValid := by
  change ∀ j : Fin 16, (retention950.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch159.valid6398
  · exact MergedCutProfiles.Batch159.valid6399
  · exact MergedCutProfiles.Batch160.valid6400
  · exact MergedCutProfiles.Batch160.valid6401
  · exact MergedCutProfiles.Batch160.valid6402
  · exact MergedCutProfiles.Batch160.valid6403
  · exact MergedCutProfiles.Batch160.valid6404
  · exact MergedCutProfiles.Batch160.valid6405
  · exact MergedCutProfiles.Batch160.valid6406
  · exact MergedCutProfiles.Batch160.valid6407
  · exact MergedCutProfiles.Batch160.valid6408
  · exact MergedCutProfiles.Batch160.valid6409
  · exact MergedCutProfiles.Batch160.valid6410
  · exact MergedCutProfiles.Batch160.valid6411
  · exact MergedCutProfiles.Batch160.valid6412
  · exact MergedCutProfiles.Batch160.valid6413
theorem numericValid950 : retention950.NumericValid := by decide +kernel
def certificate950 : RatCutBinCertificate := ⟨⟨retention950,(213756841287465781/100000000000000000),(31307344283847009/250000000000000000),(13488262449249347437/1000000000000000000),(246268246515930295277/1000000000000000000),(228520591593992317/125000000000000000)⟩,(124048331567006351/125000000000000000),(98816475019938543/250000000000000000),(23784809423709111/100000000000000000),(2627559904788879/20000000000000000)⟩
theorem valid950 : certificate950.Valid := by decide +kernel
theorem sound950 : certificate950.Sound := rat_cut_bin_certificate_sound certificate950 profilesValid950 numericValid950 valid950

def retention951 : RatCutRetentionCertificate := ⟨(203/4000),(51/1000),(2886806798547311257/9115848415521526074),(975861034163244041/500000000000000000),(31/20),(1068896474731925953897147364631404954719/780688827330595232800000000000000000000),false,MergedCutProfiles.Batch160.profile6414,(fun _ => MergedCutProfiles.Batch160.profile6414)⟩
theorem profilesValid951 : retention951.ProfilesValid := by
  exact MergedCutProfiles.Batch160.valid6414
theorem numericValid951 : retention951.NumericValid := by decide +kernel
def certificate951 : RatCutBinCertificate := ⟨⟨retention951,(213756841287465781/100000000000000000),(31307344283847009/250000000000000000),(13488262449249347437/1000000000000000000),(246268246515930295277/1000000000000000000),(133840468869822171/100000000000000000)⟩,(124048331567006351/125000000000000000),(439545153690634667/1000000000000000000),(199141820765359079/1000000000000000000),(132597643762150071/1000000000000000000)⟩
theorem valid951 : certificate951.Valid := by decide +kernel
theorem sound951 : certificate951.Sound := rat_cut_bin_certificate_sound certificate951 profilesValid951 numericValid951 valid951

def retention952 : RatCutRetentionCertificate := ⟨(203/4000),(51/1000),(1418502293146207541/3038616138507175358),(2886806798547311257/500000000000000000),1,(130968130930208845057/128000000000000000000),true,MergedCutProfiles.Batch160.profile6415,![MergedCutProfiles.Batch160.profile6415,MergedCutProfiles.Batch160.profile6416,MergedCutProfiles.Batch160.profile6417,MergedCutProfiles.Batch160.profile6418,MergedCutProfiles.Batch160.profile6419,MergedCutProfiles.Batch160.profile6420,MergedCutProfiles.Batch160.profile6421,MergedCutProfiles.Batch160.profile6422,MergedCutProfiles.Batch160.profile6423,MergedCutProfiles.Batch160.profile6424,MergedCutProfiles.Batch160.profile6425,MergedCutProfiles.Batch160.profile6426,MergedCutProfiles.Batch160.profile6427,MergedCutProfiles.Batch160.profile6428,MergedCutProfiles.Batch160.profile6429,MergedCutProfiles.Batch160.profile6430]⟩
theorem profilesValid952 : retention952.ProfilesValid := by
  change ∀ j : Fin 16, (retention952.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch160.valid6415
  · exact MergedCutProfiles.Batch160.valid6416
  · exact MergedCutProfiles.Batch160.valid6417
  · exact MergedCutProfiles.Batch160.valid6418
  · exact MergedCutProfiles.Batch160.valid6419
  · exact MergedCutProfiles.Batch160.valid6420
  · exact MergedCutProfiles.Batch160.valid6421
  · exact MergedCutProfiles.Batch160.valid6422
  · exact MergedCutProfiles.Batch160.valid6423
  · exact MergedCutProfiles.Batch160.valid6424
  · exact MergedCutProfiles.Batch160.valid6425
  · exact MergedCutProfiles.Batch160.valid6426
  · exact MergedCutProfiles.Batch160.valid6427
  · exact MergedCutProfiles.Batch160.valid6428
  · exact MergedCutProfiles.Batch160.valid6429
  · exact MergedCutProfiles.Batch160.valid6430
theorem numericValid952 : retention952.NumericValid := by decide +kernel
def certificate952 : RatCutBinCertificate := ⟨⟨retention952,(213756841287465781/100000000000000000),(31307344283847009/250000000000000000),(13488262449249347437/1000000000000000000),(246268246515930295277/1000000000000000000),(200668180137881293/200000000000000000)⟩,(124048331567006351/125000000000000000),(62066771496817021/125000000000000000),(155840721129589747/1000000000000000000),(33026977464796209/250000000000000000)⟩
theorem valid952 : certificate952.Valid := by decide +kernel
theorem sound952 : certificate952.Sound := rat_cut_bin_certificate_sound certificate952 profilesValid952 numericValid952 valid952

def retention953 : RatCutRetentionCertificate := ⟨(203/4000),(51/1000),(3011537535696852159/6077232277014350716),(4255506879438622623/500000000000000000),(21/20),(1135298053341268064143036725687898842117/1134801834516966032800000000000000000000),false,MergedCutProfiles.Batch160.profile6431,(fun _ => MergedCutProfiles.Batch160.profile6431)⟩
theorem profilesValid953 : retention953.ProfilesValid := by
  exact MergedCutProfiles.Batch160.valid6431
theorem numericValid953 : retention953.NumericValid := by decide +kernel
def certificate953 : RatCutBinCertificate := ⟨⟨retention953,(213756841287465781/100000000000000000),(31307344283847009/250000000000000000),(13488262449249347437/1000000000000000000),(246268246515930295277/1000000000000000000),(244899479953280071/250000000000000000)⟩,(124048331567006351/125000000000000000),(493462698309404281/1000000000000000000),(158000581853732261/1000000000000000000),(5295787530109851/40000000000000000)⟩
theorem valid953 : certificate953.Valid := by decide +kernel
theorem sound953 : certificate953.Sound := rat_cut_bin_certificate_sound certificate953 profilesValid953 numericValid953 valid953

def retention954 : RatCutRetentionCertificate := ⟨(203/4000),(51/1000),(1/2),(9034612607090556477/1000000000000000000),(21/20),(14356965390989901162606018938951109856511/14455380171344890363200000000000000000000),false,MergedCutProfiles.Batch160.profile6432,(fun _ => MergedCutProfiles.Batch160.profile6432)⟩
theorem profilesValid954 : retention954.ProfilesValid := by
  exact MergedCutProfiles.Batch160.valid6432
theorem numericValid954 : retention954.NumericValid := by decide +kernel
def certificate954 : RatCutBinCertificate := ⟨⟨retention954,(213756841287465781/100000000000000000),(31307344283847009/250000000000000000),(13488262449249347437/1000000000000000000),(246268246515930295277/1000000000000000000),(486176269215286193/500000000000000000)⟩,(124048331567006351/125000000000000000),(792447045995751/1600000000000000),(78360386131906889/500000000000000000),(131159082492185151/1000000000000000000)⟩
theorem valid954 : certificate954.Valid := by decide +kernel
theorem sound954 : certificate954.Sound := rat_cut_bin_certificate_sound certificate954 profilesValid954 numericValid954 valid954

def retention955 : RatCutRetentionCertificate := ⟨(203/4000),(51/1000),(1/2),64,1,(255395508330825160997279482766577882631/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch160.profile6432,(fun _ => MergedCutProfiles.Batch160.profile6432)⟩
theorem profilesValid955 : retention955.ProfilesValid := by
  exact MergedCutProfiles.Batch160.valid6432
theorem numericValid955 : retention955.NumericValid := by decide +kernel
def certificate955 : RatCutBinCertificate := ⟨⟨retention955,(213756841287465781/100000000000000000),(31307344283847009/250000000000000000),(13488262449249347437/1000000000000000000),(246268246515930295277/1000000000000000000),(977792672445333537/1000000000000000000)⟩,(124048331567006351/125000000000000000),(466698423293683003/1000000000000000000),(88821806698083527/500000000000000000),(33954048204967407/200000000000000000)⟩
theorem valid955 : certificate955.Valid := by decide +kernel
theorem sound955 : certificate955.Sound := rat_cut_bin_certificate_sound certificate955 profilesValid955 numericValid955 valid955

def retention956 : RatCutRetentionCertificate := ⟨(203/4000),(51/1000),(2066920630547128324/4557924207760763037),(1864849949614433011/500000000000000000),(6/5),(25342329596853066597352352369895015621/23310624370180412637500000000000000000),false,MergedCutProfiles.Batch160.profile6433,(fun _ => MergedCutProfiles.Batch160.profile6433)⟩
theorem profilesValid956 : retention956.ProfilesValid := by
  exact MergedCutProfiles.Batch160.valid6433
theorem numericValid956 : retention956.NumericValid := by decide +kernel
def certificate956 : RatCutBinCertificate := ⟨⟨retention956,(254993299087465781/100000000000000000),(31307344283847009/250000000000000000),(13488262449249347437/1000000000000000000),(246268246515930295277/1000000000000000000),(1058745399074030847/1000000000000000000)⟩,(990916054103918857/1000000000000000000),(96760171114227563/250000000000000000),(61392114753946669/250000000000000000),(89593151899186051/500000000000000000)⟩
theorem valid956 : certificate956.Valid := by decide +kernel
theorem sound956 : certificate956.Sound := rat_cut_bin_certificate_sound certificate956 profilesValid956 numericValid956 valid956

def retention957 : RatCutRetentionCertificate := ⟨(203/4000),(51/1000),(9042242613747468865/18231696831043052148),(516730157636782081/62500000000000000),(21/20),(825856892823861479465122444965957262839/826768252218851329600000000000000000000),false,MergedCutProfiles.Batch160.profile6434,(fun _ => MergedCutProfiles.Batch160.profile6434)⟩
theorem profilesValid957 : retention957.ProfilesValid := by
  exact MergedCutProfiles.Batch160.valid6434
theorem numericValid957 : retention957.NumericValid := by decide +kernel
def certificate957 : RatCutBinCertificate := ⟨⟨retention957,(254993299087465781/100000000000000000),(31307344283847009/250000000000000000),(13488262449249347437/1000000000000000000),(246268246515930295277/1000000000000000000),(243509527124655297/250000000000000000)⟩,(990916054103918857/1000000000000000000),(420699703992944501/1000000000000000000),(53760659818310909/250000000000000000),(178503777364047967/1000000000000000000)⟩
theorem valid957 : certificate957.Valid := by decide +kernel
theorem sound957 : certificate957.Sound := rat_cut_bin_certificate_sound certificate957 profilesValid957 numericValid957 valid957

def retention958 : RatCutRetentionCertificate := ⟨(203/4000),(51/1000),(1/2),(1808448522749493773/200000000000000000),(21/20),(574774406402586018858949507228745821439/578703527279838007360000000000000000000),false,MergedCutProfiles.Batch160.profile6432,(fun _ => MergedCutProfiles.Batch160.profile6432)⟩
theorem profilesValid958 : retention958.ProfilesValid := by
  exact MergedCutProfiles.Batch160.valid6432
theorem numericValid958 : retention958.NumericValid := by decide +kernel
def certificate958 : RatCutBinCertificate := ⟨⟨retention958,(254993299087465781/100000000000000000),(31307344283847009/250000000000000000),(13488262449249347437/1000000000000000000),(246268246515930295277/1000000000000000000),(968351025705348987/1000000000000000000)⟩,(990916054103918857/1000000000000000000),(211585227384219809/500000000000000000),(212910668369312281/1000000000000000000),(177266031730822221/1000000000000000000)⟩
theorem valid958 : certificate958.Valid := by decide +kernel
theorem sound958 : certificate958.Sound := rat_cut_bin_certificate_sound certificate958 profilesValid958 numericValid958 valid958

def retention959 : RatCutRetentionCertificate := ⟨(51/1000),(41/800),(852086281632403840/18028241671172037989),(843649783794459247/1000000000000000000),(29/10),(165211050591286299181/80000000000000000000),true,MergedCutProfiles.Batch160.profile6435,![MergedCutProfiles.Batch160.profile6435,MergedCutProfiles.Batch160.profile6436,MergedCutProfiles.Batch160.profile6437,MergedCutProfiles.Batch160.profile6438,MergedCutProfiles.Batch160.profile6439,MergedCutProfiles.Batch161.profile6440,MergedCutProfiles.Batch161.profile6441,MergedCutProfiles.Batch161.profile6442,MergedCutProfiles.Batch161.profile6443,MergedCutProfiles.Batch161.profile6444,MergedCutProfiles.Batch161.profile6445,MergedCutProfiles.Batch161.profile6446,MergedCutProfiles.Batch161.profile6447,MergedCutProfiles.Batch161.profile6448,MergedCutProfiles.Batch161.profile6449,MergedCutProfiles.Batch161.profile6450]⟩
theorem profilesValid959 : retention959.ProfilesValid := by
  change ∀ j : Fin 16, (retention959.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch160.valid6435
  · exact MergedCutProfiles.Batch160.valid6436
  · exact MergedCutProfiles.Batch160.valid6437
  · exact MergedCutProfiles.Batch160.valid6438
  · exact MergedCutProfiles.Batch160.valid6439
  · exact MergedCutProfiles.Batch161.valid6440
  · exact MergedCutProfiles.Batch161.valid6441
  · exact MergedCutProfiles.Batch161.valid6442
  · exact MergedCutProfiles.Batch161.valid6443
  · exact MergedCutProfiles.Batch161.valid6444
  · exact MergedCutProfiles.Batch161.valid6445
  · exact MergedCutProfiles.Batch161.valid6446
  · exact MergedCutProfiles.Batch161.valid6447
  · exact MergedCutProfiles.Batch161.valid6448
  · exact MergedCutProfiles.Batch161.valid6449
  · exact MergedCutProfiles.Batch161.valid6450
theorem numericValid959 : retention959.NumericValid := by decide +kernel
def certificate959 : RatCutBinCertificate := ⟨⟨retention959,(2182359126450865399/1000000000000000000),(126628854218784741/1000000000000000000),(13545089729628503117/1000000000000000000),(244546577768143902817/1000000000000000000),(2005959228755918103/1000000000000000000)⟩,(12402305880691687/12500000000000000),(1442795858986683/3906250000000000),(262764441658708843/1000000000000000000),(28076185323321159/200000000000000000)⟩
theorem valid959 : certificate959.Valid := by decide +kernel
theorem sound959 : certificate959.Sound := rat_cut_bin_certificate_sound certificate959 profilesValid959 numericValid959 valid959

def certificates : List RatCutBinCertificate := [certificate948,certificate949,certificate950,certificate951,certificate952,certificate953,certificate954,certificate955,certificate956,certificate957,certificate958,certificate959]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound948,List.forall_mem_cons.mpr ⟨sound949,List.forall_mem_cons.mpr ⟨sound950,List.forall_mem_cons.mpr ⟨sound951,List.forall_mem_cons.mpr ⟨sound952,List.forall_mem_cons.mpr ⟨sound953,List.forall_mem_cons.mpr ⟨sound954,List.forall_mem_cons.mpr ⟨sound955,List.forall_mem_cons.mpr ⟨sound956,List.forall_mem_cons.mpr ⟨sound957,List.forall_mem_cons.mpr ⟨sound958,List.forall_mem_cons.mpr ⟨sound959,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch079
