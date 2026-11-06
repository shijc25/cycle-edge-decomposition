import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch424
import Cycle12.MergedCutProfiles.Batch425
import Cycle12.MergedCutProfiles.Batch426
import Cycle12.MergedCutProfiles.Batch427
import Cycle12.MergedCutProfiles.Batch548
import Cycle12.MergedCutProfiles.Batch549
import Cycle12.MergedCutProfiles.Batch550
import Cycle12.MergedCutProfiles.Batch636
import Cycle12.MergedCutProfiles.Batch637

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch354

def retention4248 : RatCutRetentionCertificate := ⟨(8/125),(129/2000),(1/2),64,1,(63853660873591413641952829129444098831/64000000000000000000000000000000000000),false,MergedCutProfiles.Batch424.profile16984,(fun _ => MergedCutProfiles.Batch424.profile16984)⟩
theorem profilesValid4248 : retention4248.ProfilesValid := by
  exact MergedCutProfiles.Batch424.valid16984
theorem numericValid4248 : retention4248.NumericValid := by decide +kernel
def certificate4248 : RatCutBinCertificate := ⟨⟨retention4248,(66537780815368877/31250000000000000),(216862197802423917/1000000000000000000),(8548796245022962061/500000000000000000),(3604392558273399597219/1000000000000000000),(485353497718217803/500000000000000000)⟩,(15617733367844861/15625000000000000),(223887311213247253/500000000000000000),(96226864758562557/500000000000000000),(22992309974422491/125000000000000000)⟩
theorem valid4248 : certificate4248.Valid := by decide +kernel
theorem sound4248 : certificate4248.Sound := rat_cut_bin_certificate_sound certificate4248 profilesValid4248 numericValid4248 valid4248

def retention4249 : RatCutRetentionCertificate := ⟨(8/125),(129/2000),(16000000000000000000/52537530222601784183),(11688400872658513551/500000000000000000),1,(8659034735347062505585871198216387001/6233813798751207227200000000000000000),false,MergedCutProfiles.Batch636.profile25452,(fun _ => MergedCutProfiles.Batch636.profile25452)⟩
theorem profilesValid4249 : retention4249.ProfilesValid := by
  exact MergedCutProfiles.Batch636.valid25452
theorem numericValid4249 : retention4249.NumericValid := by decide +kernel
def certificate4249 : RatCutBinCertificate := ⟨⟨retention4249,(60739584377868877/31250000000000000),(216862197802423917/1000000000000000000),(8548796245022962061/500000000000000000),(3604392558273399597219/1000000000000000000),(1364389774901355293/1000000000000000000)⟩,(62473466660562331/62500000000000000),(36822287694984153/1000000000000000000),(412337966538557649/500000000000000000),(53133194010658369/50000000000000000)⟩
theorem valid4249 : certificate4249.Valid := by decide +kernel
theorem sound4249 : certificate4249.Sound := rat_cut_bin_certificate_sound certificate4249 profilesValid4249 numericValid4249 valid4249

def retention4250 : RatCutRetentionCertificate := ⟨(8/125),(129/2000),(1/2),64,1,(63853660873591413641952829129444098831/64000000000000000000000000000000000000),false,MergedCutProfiles.Batch424.profile16984,(fun _ => MergedCutProfiles.Batch424.profile16984)⟩
theorem profilesValid4250 : retention4250.ProfilesValid := by
  exact MergedCutProfiles.Batch424.valid16984
theorem numericValid4250 : retention4250.NumericValid := by decide +kernel
def certificate4250 : RatCutBinCertificate := ⟨⟨retention4250,(60739584377868877/31250000000000000),(216862197802423917/1000000000000000000),(8548796245022962061/500000000000000000),(3604392558273399597219/1000000000000000000),(973060376228344191/1000000000000000000)⟩,(62473466660562331/62500000000000000),(25815434502762429/500000000000000000),(784007631979999189/1000000000000000000),(751138564606419199/1000000000000000000)⟩
theorem valid4250 : certificate4250.Valid := by decide +kernel
theorem sound4250 : certificate4250.Sound := rat_cut_bin_certificate_sound certificate4250 profilesValid4250 numericValid4250 valid4250

def retention4251 : RatCutRetentionCertificate := ⟨(129/2000),(13/200),(822251012305596424/206276685499036750627),(162821982634771569/200000000000000000),(69/20),(18931283059711588749/8000000000000000000),true,MergedCutProfiles.Batch636.profile25453,![MergedCutProfiles.Batch636.profile25453,MergedCutProfiles.Batch636.profile25454,MergedCutProfiles.Batch636.profile25455,MergedCutProfiles.Batch636.profile25456,MergedCutProfiles.Batch636.profile25457,MergedCutProfiles.Batch636.profile25458,MergedCutProfiles.Batch636.profile25459,MergedCutProfiles.Batch636.profile25460,MergedCutProfiles.Batch636.profile25461,MergedCutProfiles.Batch636.profile25462,MergedCutProfiles.Batch636.profile25463,MergedCutProfiles.Batch425.profile17003,MergedCutProfiles.Batch636.profile25464,MergedCutProfiles.Batch636.profile25465,MergedCutProfiles.Batch636.profile25466,MergedCutProfiles.Batch548.profile21945]⟩
theorem profilesValid4251 : retention4251.ProfilesValid := by
  change ∀ j : Fin 16, (retention4251.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch636.valid25453
  · exact MergedCutProfiles.Batch636.valid25454
  · exact MergedCutProfiles.Batch636.valid25455
  · exact MergedCutProfiles.Batch636.valid25456
  · exact MergedCutProfiles.Batch636.valid25457
  · exact MergedCutProfiles.Batch636.valid25458
  · exact MergedCutProfiles.Batch636.valid25459
  · exact MergedCutProfiles.Batch636.valid25460
  · exact MergedCutProfiles.Batch636.valid25461
  · exact MergedCutProfiles.Batch636.valid25462
  · exact MergedCutProfiles.Batch636.valid25463
  · exact MergedCutProfiles.Batch425.valid17003
  · exact MergedCutProfiles.Batch636.valid25464
  · exact MergedCutProfiles.Batch636.valid25465
  · exact MergedCutProfiles.Batch636.valid25466
  · exact MergedCutProfiles.Batch548.valid21945
theorem numericValid4251 : retention4251.NumericValid := by decide +kernel
def certificate4251 : RatCutBinCertificate := ⟨⟨retention4251,(427221996322424593/200000000000000000),(55239130418189853/250000000000000000),(2157669652549067347/125000000000000000),(3571883622372616586479/1000000000000000000),(1136036463954246761/500000000000000000)⟩,(999531595577025871/1000000000000000000),(81437776267055183/200000000000000000),(113479869231493289/500000000000000000),(4840414248347253/40000000000000000)⟩
theorem valid4251 : certificate4251.Valid := by decide +kernel
theorem sound4251 : certificate4251.Sound := rat_cut_bin_certificate_sound certificate4251 profilesValid4251 numericValid4251 valid4251

def retention4252 : RatCutRetentionCertificate := ⟨(129/2000),(13/200),(1121760986000000000/206276685499036750627),(102781376538199553/125000000000000000),(69/20),(377226055398650787489/160000000000000000000),true,MergedCutProfiles.Batch636.profile25467,![MergedCutProfiles.Batch636.profile25467,MergedCutProfiles.Batch636.profile25468,MergedCutProfiles.Batch636.profile25469,MergedCutProfiles.Batch636.profile25470,MergedCutProfiles.Batch636.profile25471,MergedCutProfiles.Batch636.profile25472,MergedCutProfiles.Batch636.profile25473,MergedCutProfiles.Batch636.profile25474,MergedCutProfiles.Batch636.profile25475,MergedCutProfiles.Batch548.profile21929,MergedCutProfiles.Batch636.profile25466,MergedCutProfiles.Batch636.profile25476,MergedCutProfiles.Batch636.profile25477,MergedCutProfiles.Batch636.profile25478,MergedCutProfiles.Batch636.profile25479,MergedCutProfiles.Batch637.profile25480]⟩
theorem profilesValid4252 : retention4252.ProfilesValid := by
  change ∀ j : Fin 16, (retention4252.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch636.valid25467
  · exact MergedCutProfiles.Batch636.valid25468
  · exact MergedCutProfiles.Batch636.valid25469
  · exact MergedCutProfiles.Batch636.valid25470
  · exact MergedCutProfiles.Batch636.valid25471
  · exact MergedCutProfiles.Batch636.valid25472
  · exact MergedCutProfiles.Batch636.valid25473
  · exact MergedCutProfiles.Batch636.valid25474
  · exact MergedCutProfiles.Batch636.valid25475
  · exact MergedCutProfiles.Batch548.valid21929
  · exact MergedCutProfiles.Batch636.valid25466
  · exact MergedCutProfiles.Batch636.valid25476
  · exact MergedCutProfiles.Batch636.valid25477
  · exact MergedCutProfiles.Batch636.valid25478
  · exact MergedCutProfiles.Batch636.valid25479
  · exact MergedCutProfiles.Batch637.valid25480
theorem numericValid4252 : retention4252.NumericValid := by decide +kernel
def certificate4252 : RatCutBinCertificate := ⟨⟨retention4252,(427221996322424593/200000000000000000),(55239130418189853/250000000000000000),(2157669652549067347/125000000000000000),(3571883622372616586479/1000000000000000000),(452665082451471701/200000000000000000)⟩,(999531595577025871/1000000000000000000),(406572038470517723/1000000000000000000),(28439300645541361/125000000000000000),(121154713891307323/1000000000000000000)⟩
theorem valid4252 : certificate4252.Valid := by decide +kernel
theorem sound4252 : certificate4252.Sound := rat_cut_bin_certificate_sound certificate4252 profilesValid4252 numericValid4252 valid4252

def retention4253 : RatCutRetentionCertificate := ⟨(129/2000),(13/200),(1407208990428326416/206276685499036750627),(560880493/500000000),(53/20),(18605681843666992427/8000000000000000000),true,MergedCutProfiles.Batch637.profile25481,![MergedCutProfiles.Batch637.profile25481,MergedCutProfiles.Batch637.profile25482,MergedCutProfiles.Batch637.profile25483,MergedCutProfiles.Batch636.profile25471,MergedCutProfiles.Batch637.profile25484,MergedCutProfiles.Batch637.profile25485,MergedCutProfiles.Batch425.profile17003,MergedCutProfiles.Batch548.profile21929,MergedCutProfiles.Batch637.profile25486,MergedCutProfiles.Batch637.profile25487,MergedCutProfiles.Batch425.profile17034,MergedCutProfiles.Batch636.profile25479,MergedCutProfiles.Batch637.profile25488,MergedCutProfiles.Batch425.profile17004,MergedCutProfiles.Batch425.profile17020,MergedCutProfiles.Batch548.profile21932]⟩
theorem profilesValid4253 : retention4253.ProfilesValid := by
  change ∀ j : Fin 16, (retention4253.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch637.valid25481
  · exact MergedCutProfiles.Batch637.valid25482
  · exact MergedCutProfiles.Batch637.valid25483
  · exact MergedCutProfiles.Batch636.valid25471
  · exact MergedCutProfiles.Batch637.valid25484
  · exact MergedCutProfiles.Batch637.valid25485
  · exact MergedCutProfiles.Batch425.valid17003
  · exact MergedCutProfiles.Batch548.valid21929
  · exact MergedCutProfiles.Batch637.valid25486
  · exact MergedCutProfiles.Batch637.valid25487
  · exact MergedCutProfiles.Batch425.valid17034
  · exact MergedCutProfiles.Batch636.valid25479
  · exact MergedCutProfiles.Batch637.valid25488
  · exact MergedCutProfiles.Batch425.valid17004
  · exact MergedCutProfiles.Batch425.valid17020
  · exact MergedCutProfiles.Batch548.valid21932
theorem numericValid4253 : retention4253.NumericValid := by decide +kernel
def certificate4253 : RatCutBinCertificate := ⟨⟨retention4253,(427221996322424593/200000000000000000),(55239130418189853/250000000000000000),(2157669652549067347/125000000000000000),(3571883622372616586479/1000000000000000000),(112662410786124031/50000000000000000)⟩,(999531595577025871/1000000000000000000),(349640186246315657/1000000000000000000),(282934310345371707/1000000000000000000),(186962353072946963/1000000000000000000)⟩
theorem valid4253 : certificate4253.Valid := by decide +kernel
theorem sound4253 : certificate4253.Sound := rat_cut_bin_certificate_sound certificate4253 profilesValid4253 numericValid4253 valid4253

def retention4254 : RatCutRetentionCertificate := ⟨(129/2000),(13/200),(14015091739173083601/206276685499036750627),(87950561901770401/62500000000000000),(11/5),(162411645560052799751/80000000000000000000),true,MergedCutProfiles.Batch637.profile25487,![MergedCutProfiles.Batch637.profile25487,MergedCutProfiles.Batch637.profile25489,MergedCutProfiles.Batch637.profile25490,MergedCutProfiles.Batch637.profile25491,MergedCutProfiles.Batch637.profile25492,MergedCutProfiles.Batch425.profile17026,MergedCutProfiles.Batch425.profile17012,MergedCutProfiles.Batch637.profile25493,MergedCutProfiles.Batch637.profile25494,MergedCutProfiles.Batch426.profile17041,MergedCutProfiles.Batch549.profile21984,MergedCutProfiles.Batch637.profile25495,MergedCutProfiles.Batch637.profile25496,MergedCutProfiles.Batch637.profile25497,MergedCutProfiles.Batch637.profile25498,MergedCutProfiles.Batch426.profile17053]⟩
theorem profilesValid4254 : retention4254.ProfilesValid := by
  change ∀ j : Fin 16, (retention4254.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch637.valid25487
  · exact MergedCutProfiles.Batch637.valid25489
  · exact MergedCutProfiles.Batch637.valid25490
  · exact MergedCutProfiles.Batch637.valid25491
  · exact MergedCutProfiles.Batch637.valid25492
  · exact MergedCutProfiles.Batch425.valid17026
  · exact MergedCutProfiles.Batch425.valid17012
  · exact MergedCutProfiles.Batch637.valid25493
  · exact MergedCutProfiles.Batch637.valid25494
  · exact MergedCutProfiles.Batch426.valid17041
  · exact MergedCutProfiles.Batch549.valid21984
  · exact MergedCutProfiles.Batch637.valid25495
  · exact MergedCutProfiles.Batch637.valid25496
  · exact MergedCutProfiles.Batch637.valid25497
  · exact MergedCutProfiles.Batch637.valid25498
  · exact MergedCutProfiles.Batch426.valid17053
theorem numericValid4254 : retention4254.NumericValid := by decide +kernel
def certificate4254 : RatCutBinCertificate := ⟨⟨retention4254,(427221996322424593/200000000000000000),(55239130418189853/250000000000000000),(2157669652549067347/125000000000000000),(3571883622372616586479/1000000000000000000),(1969988475005090089/1000000000000000000)⟩,(999531595577025871/1000000000000000000),(90623257195642607/250000000000000000),(269663089543682327/1000000000000000000),(93596100779374463/500000000000000000)⟩
theorem valid4254 : certificate4254.Valid := by decide +kernel
theorem sound4254 : certificate4254.Sound := rat_cut_bin_certificate_sound certificate4254 profilesValid4254 numericValid4254 valid4254

def retention4255 : RatCutRetentionCertificate := ⟨(129/2000),(13/200),(64000000000000000000/206276685499036750627),(14015091739173083601/1000000000000000000),1,(254683338152944292791679644551379287/186867889855641114680000000000000000),false,MergedCutProfiles.Batch637.profile25499,(fun _ => MergedCutProfiles.Batch637.profile25499)⟩
theorem profilesValid4255 : retention4255.ProfilesValid := by
  exact MergedCutProfiles.Batch637.valid25499
theorem numericValid4255 : retention4255.NumericValid := by decide +kernel
def certificate4255 : RatCutBinCertificate := ⟨⟨retention4255,(427221996322424593/200000000000000000),(55239130418189853/250000000000000000),(2157669652549067347/125000000000000000),(3571883622372616586479/1000000000000000000),(667781065265948911/500000000000000000)⟩,(999531595577025871/1000000000000000000),(339551571751175103/1000000000000000000),(146840489842488113/500000000000000000),(357928132681951403/1000000000000000000)⟩
theorem valid4255 : certificate4255.Valid := by decide +kernel
theorem sound4255 : certificate4255.Sound := rat_cut_bin_certificate_sound certificate4255 profilesValid4255 numericValid4255 valid4255

def retention4256 : RatCutRetentionCertificate := ⟨(129/2000),(13/200),(1/2),64,1,(255415490385347886327351369521044328911/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch427.profile17083,(fun _ => MergedCutProfiles.Batch427.profile17083)⟩
theorem profilesValid4256 : retention4256.ProfilesValid := by
  exact MergedCutProfiles.Batch427.valid17083
theorem numericValid4256 : retention4256.NumericValid := by decide +kernel
def certificate4256 : RatCutBinCertificate := ⟨⟨retention4256,(427221996322424593/200000000000000000),(55239130418189853/250000000000000000),(2157669652549067347/125000000000000000),(3571883622372616586479/1000000000000000000),(970373145392968383/1000000000000000000)⟩,(999531595577025871/1000000000000000000),(221963061005745623/500000000000000000),(19556241192246423/100000000000000000),(93422828582455401/500000000000000000)⟩
theorem valid4256 : certificate4256.Valid := by decide +kernel
theorem sound4256 : certificate4256.Sound := rat_cut_bin_certificate_sound certificate4256 profilesValid4256 numericValid4256 valid4256

def retention4257 : RatCutRetentionCertificate := ⟨(129/2000),(13/200),(64000000000000000000/206276685499036750627),(23187650981621730537/1000000000000000000),1,(10640750542921834221608732664149853423/7729216993873910179000000000000000000),false,MergedCutProfiles.Batch637.profile25499,(fun _ => MergedCutProfiles.Batch637.profile25499)⟩
theorem profilesValid4257 : retention4257.ProfilesValid := by
  exact MergedCutProfiles.Batch637.valid25499
theorem numericValid4257 : retention4257.NumericValid := by decide +kernel
def certificate4257 : RatCutBinCertificate := ⟨⟨retention4257,(389579683922424593/200000000000000000),(55239130418189853/250000000000000000),(2157669652549067347/125000000000000000),(3571883622372616586479/1000000000000000000),(675878745154766827/500000000000000000)⟩,(999572871333485947/1000000000000000000),(37157284929926233/1000000000000000000),(411864257219141449/500000000000000000),(131460104095349231/125000000000000000)⟩
theorem valid4257 : certificate4257.Valid := by decide +kernel
theorem sound4257 : certificate4257.Sound := rat_cut_bin_certificate_sound certificate4257 profilesValid4257 numericValid4257 valid4257

def retention4258 : RatCutRetentionCertificate := ⟨(129/2000),(13/200),(1/2),64,1,(255415490385347886327351369521044328911/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch427.profile17083,(fun _ => MergedCutProfiles.Batch427.profile17083)⟩
theorem profilesValid4258 : retention4258.ProfilesValid := by
  exact MergedCutProfiles.Batch427.valid17083
theorem numericValid4258 : retention4258.NumericValid := by decide +kernel
def certificate4258 : RatCutBinCertificate := ⟨⟨retention4258,(389579683922424593/200000000000000000),(55239130418189853/250000000000000000),(2157669652549067347/125000000000000000),(3571883622372616586479/1000000000000000000),(486391188641311849/500000000000000000)⟩,(999572871333485947/1000000000000000000),(12908241194680031/250000000000000000),(784002046636532233/1000000000000000000),(375459916287973847/500000000000000000)⟩
theorem valid4258 : certificate4258.Valid := by decide +kernel
theorem sound4258 : certificate4258.Sound := rat_cut_bin_certificate_sound certificate4258 profilesValid4258 numericValid4258 valid4258

def retention4259 : RatCutRetentionCertificate := ⟨(13/200),(131/2000),(276769539867161435/67498795154922382086),(82208774217968743/100000000000000000),(69/20),(31192498531458397688457619016510730311/13153403874874998880000000000000000000),true,MergedCutProfiles.Batch637.profile25500,![MergedCutProfiles.Batch637.profile25500,MergedCutProfiles.Batch637.profile25501,MergedCutProfiles.Batch637.profile25502,MergedCutProfiles.Batch637.profile25503,MergedCutProfiles.Batch637.profile25504,MergedCutProfiles.Batch550.profile22032,MergedCutProfiles.Batch637.profile25505,MergedCutProfiles.Batch637.profile25506,MergedCutProfiles.Batch549.profile21993,MergedCutProfiles.Batch637.profile25507,MergedCutProfiles.Batch637.profile25508,MergedCutProfiles.Batch427.profile17103,MergedCutProfiles.Batch637.profile25509,MergedCutProfiles.Batch637.profile25510,MergedCutProfiles.Batch637.profile25511,MergedCutProfiles.Batch550.profile22023]⟩
theorem profilesValid4259 : retention4259.ProfilesValid := by
  change ∀ j : Fin 16, (retention4259.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch637.valid25500
  · exact MergedCutProfiles.Batch637.valid25501
  · exact MergedCutProfiles.Batch637.valid25502
  · exact MergedCutProfiles.Batch637.valid25503
  · exact MergedCutProfiles.Batch637.valid25504
  · exact MergedCutProfiles.Batch550.valid22032
  · exact MergedCutProfiles.Batch637.valid25505
  · exact MergedCutProfiles.Batch637.valid25506
  · exact MergedCutProfiles.Batch549.valid21993
  · exact MergedCutProfiles.Batch637.valid25507
  · exact MergedCutProfiles.Batch637.valid25508
  · exact MergedCutProfiles.Batch427.valid17103
  · exact MergedCutProfiles.Batch637.valid25509
  · exact MergedCutProfiles.Batch637.valid25510
  · exact MergedCutProfiles.Batch637.valid25511
  · exact MergedCutProfiles.Batch550.valid22023
theorem numericValid4259 : retention4259.NumericValid := by decide +kernel
def certificate4259 : RatCutBinCertificate := ⟨⟨retention4259,(1072522650376235353/500000000000000000),(225107070921290071/1000000000000000000),(4356874495286830139/250000000000000000),(3540212236440684184697/1000000000000000000),(1137923873707025347/500000000000000000)⟩,(999527907409721401/1000000000000000000),(397791768816085871/1000000000000000000),(29438969826323571/125000000000000000),(125971057825085757/1000000000000000000)⟩
theorem valid4259 : certificate4259.Valid := by decide +kernel
theorem sound4259 : certificate4259.Sound := rat_cut_bin_certificate_sound certificate4259 profilesValid4259 numericValid4259 valid4259

def certificates : List RatCutBinCertificate := [certificate4248,certificate4249,certificate4250,certificate4251,certificate4252,certificate4253,certificate4254,certificate4255,certificate4256,certificate4257,certificate4258,certificate4259]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound4248,List.forall_mem_cons.mpr ⟨sound4249,List.forall_mem_cons.mpr ⟨sound4250,List.forall_mem_cons.mpr ⟨sound4251,List.forall_mem_cons.mpr ⟨sound4252,List.forall_mem_cons.mpr ⟨sound4253,List.forall_mem_cons.mpr ⟨sound4254,List.forall_mem_cons.mpr ⟨sound4255,List.forall_mem_cons.mpr ⟨sound4256,List.forall_mem_cons.mpr ⟨sound4257,List.forall_mem_cons.mpr ⟨sound4258,List.forall_mem_cons.mpr ⟨sound4259,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch354
