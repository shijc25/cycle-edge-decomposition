import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch133
import Cycle12.MergedCutProfiles.Batch134
import Cycle12.MergedCutProfiles.Batch135

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch066

def retention792 : RatCutRetentionCertificate := ⟨(19/400),(191/4000),(10126209364489184431/21187119060085996196),(7077460369990681321/1000000000000000000),(11/10),(2949351323777744106297975053717581259719/2830984147996272528400000000000000000000),false,MergedCutProfiles.Batch133.profile5329,(fun _ => MergedCutProfiles.Batch133.profile5329)⟩
theorem profilesValid792 : retention792.ProfilesValid := by
  exact MergedCutProfiles.Batch133.valid5329
theorem numericValid792 : retention792.NumericValid := by decide +kernel
def certificate792 : RatCutBinCertificate := ⟨⟨retention792,(10710553993607843/5000000000000000),(107936348659400079/1000000000000000000),(12781485468971221657/1000000000000000000),(33898123835131850651/125000000000000000),(1021911769133306013/1000000000000000000)⟩,(496468725252630099/500000000000000000),(237999687779303541/500000000000000000),(85323866154889567/500000000000000000),(140565911249502769/1000000000000000000)⟩
theorem valid792 : certificate792.Valid := by decide +kernel
theorem sound792 : certificate792.Sound := rat_cut_bin_certificate_sound certificate792 profilesValid792 numericValid792 valid792

def retention793 : RatCutRetentionCertificate := ⟨(19/400),(191/4000),(10537374070786996923/21187119060085996196),(10126209364489184431/1000000000000000000),(21/20),(16212793771640069570791807151349178341159/16201934983182695089600000000000000000000),false,MergedCutProfiles.Batch133.profile5330,(fun _ => MergedCutProfiles.Batch133.profile5330)⟩
theorem profilesValid793 : retention793.ProfilesValid := by
  exact MergedCutProfiles.Batch133.valid5330
theorem numericValid793 : retention793.NumericValid := by decide +kernel
def certificate793 : RatCutBinCertificate := ⟨⟨retention793,(10710553993607843/5000000000000000),(107936348659400079/1000000000000000000),(12781485468971221657/1000000000000000000),(33898123835131850651/125000000000000000),(981675452562602291/1000000000000000000)⟩,(496468725252630099/500000000000000000),(241936938429723313/500000000000000000),(41216747696736677/250000000000000000),(14063017006140053/100000000000000000)⟩
theorem valid793 : certificate793.Valid := by decide +kernel
theorem sound793 : certificate793.Sound := rat_cut_bin_certificate_sound certificate793 profilesValid793 numericValid793 valid793

def retention794 : RatCutRetentionCertificate := ⟨(19/400),(191/4000),(1/2),(10537374070786996923/1000000000000000000),(21/20),(342768840444063146309928499828720697519/344077520678759083200000000000000000000),false,MergedCutProfiles.Batch133.profile5331,(fun _ => MergedCutProfiles.Batch133.profile5331)⟩
theorem profilesValid794 : retention794.ProfilesValid := by
  exact MergedCutProfiles.Batch133.valid5331
theorem numericValid794 : retention794.NumericValid := by decide +kernel
def certificate794 : RatCutBinCertificate := ⟨⟨retention794,(10710553993607843/5000000000000000),(107936348659400079/1000000000000000000),(12781485468971221657/1000000000000000000),(33898123835131850651/125000000000000000),(244300454719320137/250000000000000000)⟩,(496468725252630099/500000000000000000),(121257567639568879/250000000000000000),(164028912983362321/1000000000000000000),(139769714701276931/1000000000000000000)⟩
theorem valid794 : certificate794.Valid := by decide +kernel
theorem sound794 : certificate794.Sound := rat_cut_bin_certificate_sound certificate794 profilesValid794 numericValid794 valid794

def retention795 : RatCutRetentionCertificate := ⟨(19/400),(191/4000),(4744268704070708617/10593559530042998098),(752214166047347937/200000000000000000),(6/5),(4131114872812076928966099448416752501/3761070830236739685000000000000000000),false,MergedCutProfiles.Batch133.profile5332,(fun _ => MergedCutProfiles.Batch133.profile5332)⟩
theorem profilesValid795 : retention795.ProfilesValid := by
  exact MergedCutProfiles.Batch133.valid5332
theorem numericValid795 : retention795.NumericValid := by decide +kernel
def certificate795 : RatCutBinCertificate := ⟨⟨retention795,(12581524098607843/5000000000000000),(107936348659400079/1000000000000000000),(12781485468971221657/1000000000000000000),(33898123835131850651/125000000000000000),(4291544981013647/4000000000000000)⟩,(495851254442540421/500000000000000000),(93387055060463121/250000000000000000),(5172256799469849/20000000000000000),(38248214338021769/200000000000000000)⟩
theorem valid795 : certificate795.Valid := by decide +kernel
theorem sound795 : certificate795.Sound := rat_cut_bin_certificate_sound certificate795 profilesValid795 numericValid795 valid795

def retention796 : RatCutRetentionCertificate := ⟨(19/400),(191/4000),(2620312089706223497/5296779765021499049),(4744268704070708617/500000000000000000),(21/20),(3812678063887794450365356925747899565751/3795414963256566893600000000000000000000),false,MergedCutProfiles.Batch133.profile5333,(fun _ => MergedCutProfiles.Batch133.profile5333)⟩
theorem profilesValid796 : retention796.ProfilesValid := by
  exact MergedCutProfiles.Batch133.valid5333
theorem numericValid796 : retention796.NumericValid := by decide +kernel
def certificate796 : RatCutBinCertificate := ⟨⟨retention796,(12581524098607843/5000000000000000),(107936348659400079/1000000000000000000),(12781485468971221657/1000000000000000000),(33898123835131850651/125000000000000000),(98223549536384899/100000000000000000)⟩,(495851254442540421/500000000000000000),(408023075248280279/1000000000000000000),(14138194664696993/62500000000000000),(191770782372480921/1000000000000000000)⟩
theorem valid796 : certificate796.Valid := by decide +kernel
theorem sound796 : certificate796.Sound := rat_cut_bin_certificate_sound certificate796 profilesValid796 numericValid796 valid796

def retention797 : RatCutRetentionCertificate := ⟨(19/400),(191/4000),(2646515210603285732/5296779765021499049),(2620312089706223497/250000000000000000),(21/20),(5022921647956780112936694222918825437/5039061710973506725000000000000000000),false,MergedCutProfiles.Batch133.profile5334,(fun _ => MergedCutProfiles.Batch133.profile5334)⟩
theorem profilesValid797 : retention797.ProfilesValid := by
  exact MergedCutProfiles.Batch133.valid5334
theorem numericValid797 : retention797.NumericValid := by decide +kernel
def certificate797 : RatCutBinCertificate := ⟨⟨retention797,(12581524098607843/5000000000000000),(107936348659400079/1000000000000000000),(12781485468971221657/1000000000000000000),(33898123835131850651/125000000000000000),(974484180758168803/1000000000000000000)⟩,(495851254442540421/500000000000000000),(411268602764351277/1000000000000000000),(223314695081256783/1000000000000000000),(189484141405727259/1000000000000000000)⟩
theorem valid797 : certificate797.Valid := by decide +kernel
theorem sound797 : certificate797.Sound := rat_cut_bin_certificate_sound certificate797 profilesValid797 numericValid797 valid797

def retention798 : RatCutRetentionCertificate := ⟨(19/400),(191/4000),(1/2),(661628802650821433/62500000000000000),(21/20),(1054663386982703015858785600187825829111/1058606084241314292800000000000000000000),false,MergedCutProfiles.Batch133.profile5331,(fun _ => MergedCutProfiles.Batch133.profile5331)⟩
theorem profilesValid798 : retention798.ProfilesValid := by
  exact MergedCutProfiles.Batch133.valid5331
theorem numericValid798 : retention798.NumericValid := by decide +kernel
def certificate798 : RatCutBinCertificate := ⟨⟨retention798,(12581524098607843/5000000000000000),(107936348659400079/1000000000000000000),(12781485468971221657/1000000000000000000),(33898123835131850651/125000000000000000),(486981377555596387/500000000000000000)⟩,(495851254442540421/500000000000000000),(41148878161220963/100000000000000000),(223119129616040137/1000000000000000000),(94685558776096749/500000000000000000)⟩
theorem valid798 : certificate798.Valid := by decide +kernel
theorem sound798 : certificate798.Sound := rat_cut_bin_certificate_sound certificate798 profilesValid798 numericValid798 valid798

def retention799 : RatCutRetentionCertificate := ⟨(191/4000),(6/125),(418862078321232304/10468701106791427219),(414714929030923073/500000000000000000),3,(268211896013973769033/128000000000000000000),true,MergedCutProfiles.Batch133.profile5335,![MergedCutProfiles.Batch133.profile5335,MergedCutProfiles.Batch133.profile5336,MergedCutProfiles.Batch133.profile5337,MergedCutProfiles.Batch133.profile5338,MergedCutProfiles.Batch133.profile5339,MergedCutProfiles.Batch133.profile5340,MergedCutProfiles.Batch133.profile5341,MergedCutProfiles.Batch133.profile5342,MergedCutProfiles.Batch133.profile5343,MergedCutProfiles.Batch133.profile5344,MergedCutProfiles.Batch133.profile5345,MergedCutProfiles.Batch133.profile5346,MergedCutProfiles.Batch133.profile5347,MergedCutProfiles.Batch133.profile5348,MergedCutProfiles.Batch133.profile5349,MergedCutProfiles.Batch133.profile5350]⟩
theorem profilesValid799 : retention799.ProfilesValid := by
  change ∀ j : Fin 16, (retention799.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch133.valid5335
  · exact MergedCutProfiles.Batch133.valid5336
  · exact MergedCutProfiles.Batch133.valid5337
  · exact MergedCutProfiles.Batch133.valid5338
  · exact MergedCutProfiles.Batch133.valid5339
  · exact MergedCutProfiles.Batch133.valid5340
  · exact MergedCutProfiles.Batch133.valid5341
  · exact MergedCutProfiles.Batch133.valid5342
  · exact MergedCutProfiles.Batch133.valid5343
  · exact MergedCutProfiles.Batch133.valid5344
  · exact MergedCutProfiles.Batch133.valid5345
  · exact MergedCutProfiles.Batch133.valid5346
  · exact MergedCutProfiles.Batch133.valid5347
  · exact MergedCutProfiles.Batch133.valid5348
  · exact MergedCutProfiles.Batch133.valid5349
  · exact MergedCutProfiles.Batch133.valid5350
theorem numericValid799 : retention799.NumericValid := by decide +kernel
def certificate799 : RatCutBinCertificate := ⟨⟨retention799,(2142735331094584143/1000000000000000000),(13651068898300767/125000000000000000),(12833819923278311389/1000000000000000000),(134543316774886799319/500000000000000000),(2040696117340548209/1000000000000000000)⟩,(992890240178094193/1000000000000000000),(189528349032638471/500000000000000000),(25322945386941083/100000000000000000),(134136976731524091/1000000000000000000)⟩
theorem valid799 : certificate799.Valid := by decide +kernel
theorem sound799 : certificate799.Sound := rat_cut_bin_certificate_sound certificate799 profilesValid799 numericValid799 valid799

def retention800 : RatCutRetentionCertificate := ⟨(191/4000),(6/125),(435588320500000000/10468701106791427219),(26178879895077019/31250000000000000),(59/20),(20855619116670169259/10000000000000000000),true,MergedCutProfiles.Batch133.profile5351,![MergedCutProfiles.Batch133.profile5351,MergedCutProfiles.Batch133.profile5352,MergedCutProfiles.Batch133.profile5353,MergedCutProfiles.Batch133.profile5354,MergedCutProfiles.Batch133.profile5355,MergedCutProfiles.Batch133.profile5356,MergedCutProfiles.Batch133.profile5357,MergedCutProfiles.Batch133.profile5358,MergedCutProfiles.Batch133.profile5359,MergedCutProfiles.Batch134.profile5360,MergedCutProfiles.Batch134.profile5361,MergedCutProfiles.Batch134.profile5362,MergedCutProfiles.Batch134.profile5363,MergedCutProfiles.Batch134.profile5364,MergedCutProfiles.Batch134.profile5365,MergedCutProfiles.Batch134.profile5366]⟩
theorem profilesValid800 : retention800.ProfilesValid := by
  change ∀ j : Fin 16, (retention800.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch133.valid5351
  · exact MergedCutProfiles.Batch133.valid5352
  · exact MergedCutProfiles.Batch133.valid5353
  · exact MergedCutProfiles.Batch133.valid5354
  · exact MergedCutProfiles.Batch133.valid5355
  · exact MergedCutProfiles.Batch133.valid5356
  · exact MergedCutProfiles.Batch133.valid5357
  · exact MergedCutProfiles.Batch133.valid5358
  · exact MergedCutProfiles.Batch133.valid5359
  · exact MergedCutProfiles.Batch134.valid5360
  · exact MergedCutProfiles.Batch134.valid5361
  · exact MergedCutProfiles.Batch134.valid5362
  · exact MergedCutProfiles.Batch134.valid5363
  · exact MergedCutProfiles.Batch134.valid5364
  · exact MergedCutProfiles.Batch134.valid5365
  · exact MergedCutProfiles.Batch134.valid5366
theorem numericValid800 : retention800.NumericValid := by decide +kernel
def certificate800 : RatCutBinCertificate := ⟨⟨retention800,(2142735331094584143/1000000000000000000),(13651068898300767/125000000000000000),(12833819923278311389/1000000000000000000),(134543316774886799319/500000000000000000),(1015882176520317799/500000000000000000)⟩,(992890240178094193/1000000000000000000),(379135420636295227/1000000000000000000),(253153101491569739/1000000000000000000),(27041404108407209/200000000000000000)⟩
theorem valid800 : certificate800.Valid := by decide +kernel
theorem sound800 : certificate800.Sound := rat_cut_bin_certificate_sound certificate800 profilesValid800 numericValid800 valid800

def retention801 : RatCutRetentionCertificate := ⟨(191/4000),(6/125),(972571739025415163/20937402213582854438),(871176641/1000000000),(57/20),(16537468870583060289/8000000000000000000),true,MergedCutProfiles.Batch134.profile5367,![MergedCutProfiles.Batch134.profile5367,MergedCutProfiles.Batch134.profile5368,MergedCutProfiles.Batch134.profile5369,MergedCutProfiles.Batch134.profile5370,MergedCutProfiles.Batch134.profile5371,MergedCutProfiles.Batch133.profile5341,MergedCutProfiles.Batch134.profile5372,MergedCutProfiles.Batch134.profile5373,MergedCutProfiles.Batch134.profile5374,MergedCutProfiles.Batch134.profile5375,MergedCutProfiles.Batch134.profile5376,MergedCutProfiles.Batch134.profile5377,MergedCutProfiles.Batch134.profile5378,MergedCutProfiles.Batch134.profile5379,MergedCutProfiles.Batch134.profile5380,MergedCutProfiles.Batch134.profile5381]⟩
theorem profilesValid801 : retention801.ProfilesValid := by
  change ∀ j : Fin 16, (retention801.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch134.valid5367
  · exact MergedCutProfiles.Batch134.valid5368
  · exact MergedCutProfiles.Batch134.valid5369
  · exact MergedCutProfiles.Batch134.valid5370
  · exact MergedCutProfiles.Batch134.valid5371
  · exact MergedCutProfiles.Batch133.valid5341
  · exact MergedCutProfiles.Batch134.valid5372
  · exact MergedCutProfiles.Batch134.valid5373
  · exact MergedCutProfiles.Batch134.valid5374
  · exact MergedCutProfiles.Batch134.valid5375
  · exact MergedCutProfiles.Batch134.valid5376
  · exact MergedCutProfiles.Batch134.valid5377
  · exact MergedCutProfiles.Batch134.valid5378
  · exact MergedCutProfiles.Batch134.valid5379
  · exact MergedCutProfiles.Batch134.valid5380
  · exact MergedCutProfiles.Batch134.valid5381
theorem numericValid801 : retention801.NumericValid := by decide +kernel
def certificate801 : RatCutBinCertificate := ⟨⟨retention801,(2142735331094584143/1000000000000000000),(13651068898300767/125000000000000000),(12833819923278311389/1000000000000000000),(134543316774886799319/500000000000000000),(503802434002565431/250000000000000000)⟩,(992890240178094193/1000000000000000000),(376103485503894627/1000000000000000000),(25610558184987873/100000000000000000),(6988261814883759/50000000000000000)⟩
theorem valid801 : certificate801.Valid := by decide +kernel
theorem sound801 : certificate801.Sound := rat_cut_bin_certificate_sound certificate801 profilesValid801 numericValid801 valid801

def retention802 : RatCutRetentionCertificate := ⟨(191/4000),(6/125),(901190955769516166/10468701106791427219),(972571739025415163/1000000000000000000),(13/5),(2484518267745221668679/1280000000000000000000),true,MergedCutProfiles.Batch134.profile5382,![MergedCutProfiles.Batch134.profile5382,MergedCutProfiles.Batch134.profile5383,MergedCutProfiles.Batch134.profile5384,MergedCutProfiles.Batch134.profile5385,MergedCutProfiles.Batch134.profile5386,MergedCutProfiles.Batch134.profile5387,MergedCutProfiles.Batch134.profile5378,MergedCutProfiles.Batch134.profile5388,MergedCutProfiles.Batch134.profile5389,MergedCutProfiles.Batch134.profile5390,MergedCutProfiles.Batch134.profile5391,MergedCutProfiles.Batch134.profile5392,MergedCutProfiles.Batch134.profile5393,MergedCutProfiles.Batch134.profile5394,MergedCutProfiles.Batch134.profile5395,MergedCutProfiles.Batch134.profile5396]⟩
theorem profilesValid802 : retention802.ProfilesValid := by
  change ∀ j : Fin 16, (retention802.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch134.valid5382
  · exact MergedCutProfiles.Batch134.valid5383
  · exact MergedCutProfiles.Batch134.valid5384
  · exact MergedCutProfiles.Batch134.valid5385
  · exact MergedCutProfiles.Batch134.valid5386
  · exact MergedCutProfiles.Batch134.valid5387
  · exact MergedCutProfiles.Batch134.valid5378
  · exact MergedCutProfiles.Batch134.valid5388
  · exact MergedCutProfiles.Batch134.valid5389
  · exact MergedCutProfiles.Batch134.valid5390
  · exact MergedCutProfiles.Batch134.valid5391
  · exact MergedCutProfiles.Batch134.valid5392
  · exact MergedCutProfiles.Batch134.valid5393
  · exact MergedCutProfiles.Batch134.valid5394
  · exact MergedCutProfiles.Batch134.valid5395
  · exact MergedCutProfiles.Batch134.valid5396
theorem numericValid802 : retention802.NumericValid := by decide +kernel
def certificate802 : RatCutBinCertificate := ⟨⟨retention802,(2142735331094584143/1000000000000000000),(13651068898300767/125000000000000000),(12833819923278311389/1000000000000000000),(134543316774886799319/500000000000000000),(1893615275969535287/1000000000000000000)⟩,(992890240178094193/1000000000000000000),(383176746968771413/1000000000000000000),(9970212714109459/40000000000000000),(6988089432479461/50000000000000000)⟩
theorem valid802 : certificate802.Valid := by decide +kernel
theorem sound802 : certificate802.Sound := rat_cut_bin_certificate_sound certificate802 profilesValid802 numericValid802 valid802

def retention803 : RatCutRetentionCertificate := ⟨(191/4000),(6/125),(2974278819930026646/10468701106791427219),(450595477884758083/250000000000000000),(33/20),(461232250469307700131/320000000000000000000),true,MergedCutProfiles.Batch134.profile5397,![MergedCutProfiles.Batch134.profile5397,MergedCutProfiles.Batch134.profile5398,MergedCutProfiles.Batch134.profile5399,MergedCutProfiles.Batch135.profile5400,MergedCutProfiles.Batch135.profile5401,MergedCutProfiles.Batch135.profile5402,MergedCutProfiles.Batch135.profile5403,MergedCutProfiles.Batch135.profile5404,MergedCutProfiles.Batch135.profile5405,MergedCutProfiles.Batch135.profile5406,MergedCutProfiles.Batch135.profile5407,MergedCutProfiles.Batch135.profile5408,MergedCutProfiles.Batch135.profile5409,MergedCutProfiles.Batch135.profile5410,MergedCutProfiles.Batch135.profile5411,MergedCutProfiles.Batch135.profile5412]⟩
theorem profilesValid803 : retention803.ProfilesValid := by
  change ∀ j : Fin 16, (retention803.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch134.valid5397
  · exact MergedCutProfiles.Batch134.valid5398
  · exact MergedCutProfiles.Batch134.valid5399
  · exact MergedCutProfiles.Batch135.valid5400
  · exact MergedCutProfiles.Batch135.valid5401
  · exact MergedCutProfiles.Batch135.valid5402
  · exact MergedCutProfiles.Batch135.valid5403
  · exact MergedCutProfiles.Batch135.valid5404
  · exact MergedCutProfiles.Batch135.valid5405
  · exact MergedCutProfiles.Batch135.valid5406
  · exact MergedCutProfiles.Batch135.valid5407
  · exact MergedCutProfiles.Batch135.valid5408
  · exact MergedCutProfiles.Batch135.valid5409
  · exact MergedCutProfiles.Batch135.valid5410
  · exact MergedCutProfiles.Batch135.valid5411
  · exact MergedCutProfiles.Batch135.valid5412
theorem numericValid803 : retention803.NumericValid := by decide +kernel
def certificate803 : RatCutBinCertificate := ⟨⟨retention803,(2142735331094584143/1000000000000000000),(13651068898300767/125000000000000000),(12833819923278311389/1000000000000000000),(134543316774886799319/500000000000000000),(7056307289398111/5000000000000000)⟩,(992890240178094193/1000000000000000000),(423500755749943977/1000000000000000000),(212626751714689699/1000000000000000000),(28016931366298217/200000000000000000)⟩
theorem valid803 : certificate803.Valid := by decide +kernel
theorem sound803 : certificate803.Sound := rat_cut_bin_certificate_sound certificate803 profilesValid803 numericValid803 valid803

def certificates : List RatCutBinCertificate := [certificate792,certificate793,certificate794,certificate795,certificate796,certificate797,certificate798,certificate799,certificate800,certificate801,certificate802,certificate803]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound792,List.forall_mem_cons.mpr ⟨sound793,List.forall_mem_cons.mpr ⟨sound794,List.forall_mem_cons.mpr ⟨sound795,List.forall_mem_cons.mpr ⟨sound796,List.forall_mem_cons.mpr ⟨sound797,List.forall_mem_cons.mpr ⟨sound798,List.forall_mem_cons.mpr ⟨sound799,List.forall_mem_cons.mpr ⟨sound800,List.forall_mem_cons.mpr ⟨sound801,List.forall_mem_cons.mpr ⟨sound802,List.forall_mem_cons.mpr ⟨sound803,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch066
