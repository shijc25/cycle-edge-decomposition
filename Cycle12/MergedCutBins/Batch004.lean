import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch008
import Cycle12.MergedCutProfiles.Batch009
import Cycle12.MergedCutProfiles.Batch010
import Cycle12.MergedCutProfiles.Batch011

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch004

def retention48 : RatCutRetentionCertificate := ⟨(7/1000),(1/125),(3200000000000000000/46065997685764341929),(3260787563140408713/1000000000000000000),(27/20),(10091163324022277944991833515725796805319/5217260101024653940800000000000000000000),false,MergedCutProfiles.Batch008.profile354,(fun _ => MergedCutProfiles.Batch008.profile354)⟩
theorem profilesValid48 : retention48.ProfilesValid := by
  exact MergedCutProfiles.Batch008.valid354
theorem numericValid48 : retention48.NumericValid := by decide +kernel
def certificate48 : RatCutBinCertificate := ⟨⟨retention48,(2173232172264357003/1000000000000000000),(1291114465089419/500000000000000000),(290195100374488423/40000000000000000),(839228398002528746119/125000000000000000),(1933144026468339839/1000000000000000000)⟩,(999676942712047147/1000000000000000000),(204697021919813127/1000000000000000000),(470343157161284717/1000000000000000000),(508021461314429247/1000000000000000000)⟩
theorem valid48 : certificate48.Valid := by decide +kernel
theorem sound48 : certificate48.Sound := rat_cut_bin_certificate_sound certificate48 profilesValid48 numericValid48 valid48

def retention49 : RatCutRetentionCertificate := ⟨(7/1000),(1/125),(1/2),64,1,(255368898673698792760224881759734912191/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch008.profile355,(fun _ => MergedCutProfiles.Batch008.profile355)⟩
theorem profilesValid49 : retention49.ProfilesValid := by
  exact MergedCutProfiles.Batch008.valid355
theorem numericValid49 : retention49.NumericValid := by decide +kernel
def certificate49 : RatCutBinCertificate := ⟨⟨retention49,(2173232172264357003/1000000000000000000),(1291114465089419/500000000000000000),(290195100374488423/40000000000000000),(839228398002528746119/125000000000000000),(498380620899550167/500000000000000000)⟩,(999676942712047147/1000000000000000000),(317595675727449/800000000000000),(236247379265325491/1000000000000000000),(115897770341932859/500000000000000000)⟩
theorem valid49 : certificate49.Valid := by decide +kernel
theorem sound49 : certificate49.Sound := rat_cut_bin_certificate_sound certificate49 profilesValid49 numericValid49 valid49

def retention50 : RatCutRetentionCertificate := ⟨(1/125),(9/1000),(608117419511463736/724711077206995317255),(584388887288127723/1000000000000000000),4,(1622184032769840016863283379942491/730486109110159653750000000000000),true,MergedCutProfiles.Batch008.profile356,![MergedCutProfiles.Batch008.profile356,MergedCutProfiles.Batch008.profile357,MergedCutProfiles.Batch008.profile358,MergedCutProfiles.Batch008.profile359,MergedCutProfiles.Batch009.profile360,MergedCutProfiles.Batch009.profile361,MergedCutProfiles.Batch009.profile362,MergedCutProfiles.Batch009.profile363,MergedCutProfiles.Batch009.profile364,MergedCutProfiles.Batch009.profile365,MergedCutProfiles.Batch009.profile366,MergedCutProfiles.Batch009.profile367,MergedCutProfiles.Batch009.profile368,MergedCutProfiles.Batch009.profile369,MergedCutProfiles.Batch009.profile370,MergedCutProfiles.Batch009.profile371]⟩
theorem profilesValid50 : retention50.ProfilesValid := by
  change ∀ j : Fin 16, (retention50.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch008.valid356
  · exact MergedCutProfiles.Batch008.valid357
  · exact MergedCutProfiles.Batch008.valid358
  · exact MergedCutProfiles.Batch008.valid359
  · exact MergedCutProfiles.Batch009.valid360
  · exact MergedCutProfiles.Batch009.valid361
  · exact MergedCutProfiles.Batch009.valid362
  · exact MergedCutProfiles.Batch009.valid363
  · exact MergedCutProfiles.Batch009.valid364
  · exact MergedCutProfiles.Batch009.valid365
  · exact MergedCutProfiles.Batch009.valid366
  · exact MergedCutProfiles.Batch009.valid367
  · exact MergedCutProfiles.Batch009.valid368
  · exact MergedCutProfiles.Batch009.valid369
  · exact MergedCutProfiles.Batch009.valid370
  · exact MergedCutProfiles.Batch009.valid371
theorem numericValid50 : retention50.NumericValid := by decide +kernel
def certificate50 : RatCutBinCertificate := ⟨⟨retention50,(230245934779840367/125000000000000000),(3278736788116277/1000000000000000000),(3671580180914186761/500000000000000000),(2672750682344156463489/500000000000000000),(221740137273370349/100000000000000000)⟩,(999656306750827427/1000000000000000000),(556655875975127119/1000000000000000000),(1172506265142253/10000000000000000),(10503397168055161/200000000000000000)⟩
theorem valid50 : certificate50.Valid := by decide +kernel
theorem sound50 : certificate50.Sound := rat_cut_bin_certificate_sound certificate50 profilesValid50 numericValid50 valid50

def retention51 : RatCutRetentionCertificate := ⟨(1/125),(9/1000),(256699248800000000/144942215441399063451),(76014677438932967/125000000000000000),4,(72067136757592074977/32000000000000000000),true,MergedCutProfiles.Batch009.profile372,![MergedCutProfiles.Batch009.profile372,MergedCutProfiles.Batch009.profile373,MergedCutProfiles.Batch009.profile374,MergedCutProfiles.Batch009.profile375,MergedCutProfiles.Batch009.profile376,MergedCutProfiles.Batch009.profile377,MergedCutProfiles.Batch009.profile370,MergedCutProfiles.Batch009.profile378,MergedCutProfiles.Batch009.profile379,MergedCutProfiles.Batch009.profile380,MergedCutProfiles.Batch009.profile381,MergedCutProfiles.Batch009.profile382,MergedCutProfiles.Batch009.profile383,MergedCutProfiles.Batch009.profile384,MergedCutProfiles.Batch009.profile385,MergedCutProfiles.Batch009.profile386]⟩
theorem profilesValid51 : retention51.ProfilesValid := by
  change ∀ j : Fin 16, (retention51.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch009.valid372
  · exact MergedCutProfiles.Batch009.valid373
  · exact MergedCutProfiles.Batch009.valid374
  · exact MergedCutProfiles.Batch009.valid375
  · exact MergedCutProfiles.Batch009.valid376
  · exact MergedCutProfiles.Batch009.valid377
  · exact MergedCutProfiles.Batch009.valid370
  · exact MergedCutProfiles.Batch009.valid378
  · exact MergedCutProfiles.Batch009.valid379
  · exact MergedCutProfiles.Batch009.valid380
  · exact MergedCutProfiles.Batch009.valid381
  · exact MergedCutProfiles.Batch009.valid382
  · exact MergedCutProfiles.Batch009.valid383
  · exact MergedCutProfiles.Batch009.valid384
  · exact MergedCutProfiles.Batch009.valid385
  · exact MergedCutProfiles.Batch009.valid386
theorem numericValid51 : retention51.NumericValid := by decide +kernel
def certificate51 : RatCutBinCertificate := ⟨⟨retention51,(230245934779840367/125000000000000000),(3278736788116277/1000000000000000000),(3671580180914186761/500000000000000000),(2672750682344156463489/500000000000000000),(89952330127589417/40000000000000000)⟩,(999656306750827427/1000000000000000000),(267320277699212391/500000000000000000),(6529428521314067/50000000000000000),(59610023987537723/1000000000000000000)⟩
theorem valid51 : certificate51.Valid := by decide +kernel
theorem sound51 : certificate51.Sound := rat_cut_bin_certificate_sound certificate51 profilesValid51 numericValid51 valid51

def retention52 : RatCutRetentionCertificate := ⟨(1/125),(9/1000),(2473438675634632267/724711077206995317255),(320874061/250000000),(12/5),(36580339027567402267/16000000000000000000),true,MergedCutProfiles.Batch008.profile359,![MergedCutProfiles.Batch008.profile359,MergedCutProfiles.Batch009.profile387,MergedCutProfiles.Batch009.profile367,MergedCutProfiles.Batch009.profile371,MergedCutProfiles.Batch009.profile388,MergedCutProfiles.Batch009.profile389,MergedCutProfiles.Batch009.profile390,MergedCutProfiles.Batch009.profile391,MergedCutProfiles.Batch009.profile392,MergedCutProfiles.Batch009.profile393,MergedCutProfiles.Batch009.profile394,MergedCutProfiles.Batch009.profile395,MergedCutProfiles.Batch009.profile396,MergedCutProfiles.Batch009.profile397,MergedCutProfiles.Batch009.profile398,MergedCutProfiles.Batch009.profile399]⟩
theorem profilesValid52 : retention52.ProfilesValid := by
  change ∀ j : Fin 16, (retention52.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch008.valid359
  · exact MergedCutProfiles.Batch009.valid387
  · exact MergedCutProfiles.Batch009.valid367
  · exact MergedCutProfiles.Batch009.valid371
  · exact MergedCutProfiles.Batch009.valid388
  · exact MergedCutProfiles.Batch009.valid389
  · exact MergedCutProfiles.Batch009.valid390
  · exact MergedCutProfiles.Batch009.valid391
  · exact MergedCutProfiles.Batch009.valid392
  · exact MergedCutProfiles.Batch009.valid393
  · exact MergedCutProfiles.Batch009.valid394
  · exact MergedCutProfiles.Batch009.valid395
  · exact MergedCutProfiles.Batch009.valid396
  · exact MergedCutProfiles.Batch009.valid397
  · exact MergedCutProfiles.Batch009.valid398
  · exact MergedCutProfiles.Batch009.valid399
theorem numericValid52 : retention52.NumericValid := by decide +kernel
def certificate52 : RatCutBinCertificate := ⟨⟨retention52,(230245934779840367/125000000000000000),(3278736788116277/1000000000000000000),(3671580180914186761/500000000000000000),(2672750682344156463489/500000000000000000),(2284297327036642161/1000000000000000000)⟩,(999656306750827427/1000000000000000000),(21540402287918447/62500000000000000),(144108469549630791/500000000000000000),(104743516796518251/500000000000000000)⟩
theorem valid52 : certificate52.Valid := by decide +kernel
theorem sound52 : certificate52.Sound := rat_cut_bin_certificate_sound certificate52 profilesValid52 numericValid52 valid52

def retention53 : RatCutRetentionCertificate := ⟨(1/125),(9/1000),(12800000000000000000/144942215441399063451),(2473438675634632267/1000000000000000000),(8/5),(2445367112944940876951/1280000000000000000000),true,MergedCutProfiles.Batch010.profile400,![MergedCutProfiles.Batch010.profile400,MergedCutProfiles.Batch010.profile401,MergedCutProfiles.Batch010.profile402,MergedCutProfiles.Batch010.profile403,MergedCutProfiles.Batch010.profile404,MergedCutProfiles.Batch010.profile405,MergedCutProfiles.Batch010.profile406,MergedCutProfiles.Batch010.profile407,MergedCutProfiles.Batch010.profile408,MergedCutProfiles.Batch010.profile409,MergedCutProfiles.Batch010.profile410,MergedCutProfiles.Batch010.profile411,MergedCutProfiles.Batch010.profile412,MergedCutProfiles.Batch010.profile413,MergedCutProfiles.Batch010.profile414,MergedCutProfiles.Batch010.profile415]⟩
theorem profilesValid53 : retention53.ProfilesValid := by
  change ∀ j : Fin 16, (retention53.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch010.valid400
  · exact MergedCutProfiles.Batch010.valid401
  · exact MergedCutProfiles.Batch010.valid402
  · exact MergedCutProfiles.Batch010.valid403
  · exact MergedCutProfiles.Batch010.valid404
  · exact MergedCutProfiles.Batch010.valid405
  · exact MergedCutProfiles.Batch010.valid406
  · exact MergedCutProfiles.Batch010.valid407
  · exact MergedCutProfiles.Batch010.valid408
  · exact MergedCutProfiles.Batch010.valid409
  · exact MergedCutProfiles.Batch010.valid410
  · exact MergedCutProfiles.Batch010.valid411
  · exact MergedCutProfiles.Batch010.valid412
  · exact MergedCutProfiles.Batch010.valid413
  · exact MergedCutProfiles.Batch010.valid414
  · exact MergedCutProfiles.Batch010.valid415
theorem numericValid53 : retention53.NumericValid := by decide +kernel
def certificate53 : RatCutBinCertificate := ⟨⟨retention53,(230245934779840367/125000000000000000),(3278736788116277/1000000000000000000),(3671580180914186761/500000000000000000),(2672750682344156463489/500000000000000000),(954563574461046993/500000000000000000)⟩,(999656306750827427/1000000000000000000),(39775643587215689/125000000000000000),(63483423781718981/200000000000000000),(290893780250797013/1000000000000000000)⟩
theorem valid53 : certificate53.Valid := by decide +kernel
theorem sound53 : certificate53.Sound := rat_cut_bin_certificate_sound certificate53 profilesValid53 numericValid53 valid53

def retention54 : RatCutRetentionCertificate := ⟨(1/125),(9/1000),(1/2),64,1,(249383750761872694322254949188936071/250000000000000000000000000000000000),false,MergedCutProfiles.Batch010.profile416,(fun _ => MergedCutProfiles.Batch010.profile416)⟩
theorem profilesValid54 : retention54.ProfilesValid := by
  exact MergedCutProfiles.Batch010.valid416
theorem numericValid54 : retention54.NumericValid := by decide +kernel
def certificate54 : RatCutBinCertificate := ⟨⟨retention54,(230245934779840367/125000000000000000),(3278736788116277/1000000000000000000),(3671580180914186761/500000000000000000),(2672750682344156463489/500000000000000000),(996712560625738859/1000000000000000000)⟩,(999656306750827427/1000000000000000000),(422461946741351719/1000000000000000000),(213520549934193589/1000000000000000000),(209482452220912743/1000000000000000000)⟩
theorem valid54 : certificate54.Valid := by decide +kernel
theorem sound54 : certificate54.Sound := rat_cut_bin_certificate_sound certificate54 profilesValid54 numericValid54 valid54

def retention55 : RatCutRetentionCertificate := ⟨(1/125),(9/1000),(12800000000000000000/144942215441399063451),(3216207583754941/976562500000000),(27/20),(151417138259097075343990410960518951/80405189593873525000000000000000000),false,MergedCutProfiles.Batch010.profile417,(fun _ => MergedCutProfiles.Batch010.profile417)⟩
theorem profilesValid55 : retention55.ProfilesValid := by
  exact MergedCutProfiles.Batch010.valid417
theorem numericValid55 : retention55.NumericValid := by decide +kernel
def certificate55 : RatCutBinCertificate := ⟨⟨retention55,(273154362279840367/125000000000000000),(3278736788116277/1000000000000000000),(3671580180914186761/500000000000000000),(2672750682344156463489/500000000000000000),(470464743591301217/250000000000000000)⟩,(999592256315166341/1000000000000000000),(208542046764322977/1000000000000000000),(232151975993964867/500000000000000000),(123130452852913479/250000000000000000)⟩
theorem valid55 : certificate55.Valid := by decide +kernel
theorem sound55 : certificate55.Sound := rat_cut_bin_certificate_sound certificate55 profilesValid55 numericValid55 valid55

def retention56 : RatCutRetentionCertificate := ⟨(1/125),(9/1000),(1/2),64,1,(249383750761872694322254949188936071/250000000000000000000000000000000000),false,MergedCutProfiles.Batch010.profile416,(fun _ => MergedCutProfiles.Batch010.profile416)⟩
theorem profilesValid56 : retention56.ProfilesValid := by
  exact MergedCutProfiles.Batch010.valid416
theorem numericValid56 : retention56.NumericValid := by decide +kernel
def certificate56 : RatCutBinCertificate := ⟨⟨retention56,(273154362279840367/125000000000000000),(3278736788116277/1000000000000000000),(3671580180914186761/500000000000000000),(2672750682344156463489/500000000000000000),(49827964549397369/50000000000000000)⟩,(999592256315166341/1000000000000000000),(78760335844518411/200000000000000000),(239209824626569191/1000000000000000000),(46927064300680481/200000000000000000)⟩
theorem valid56 : certificate56.Valid := by decide +kernel
theorem sound56 : certificate56.Sound := rat_cut_bin_certificate_sound certificate56 profilesValid56 numericValid56 valid56

def retention57 : RatCutRetentionCertificate := ⟨(9/1000),(1/100),(619018969490984151/584384071637180572724),(588975309448360287/1000000000000000000),4,(8910216685494925363/4000000000000000000),true,MergedCutProfiles.Batch010.profile418,![MergedCutProfiles.Batch010.profile418,MergedCutProfiles.Batch010.profile419,MergedCutProfiles.Batch010.profile420,MergedCutProfiles.Batch010.profile421,MergedCutProfiles.Batch010.profile422,MergedCutProfiles.Batch010.profile423,MergedCutProfiles.Batch010.profile424,MergedCutProfiles.Batch010.profile425,MergedCutProfiles.Batch010.profile426,MergedCutProfiles.Batch010.profile427,MergedCutProfiles.Batch010.profile428,MergedCutProfiles.Batch010.profile429,MergedCutProfiles.Batch010.profile430,MergedCutProfiles.Batch010.profile431,MergedCutProfiles.Batch010.profile432,MergedCutProfiles.Batch010.profile433]⟩
theorem profilesValid57 : retention57.ProfilesValid := by
  change ∀ j : Fin 16, (retention57.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch010.valid418
  · exact MergedCutProfiles.Batch010.valid419
  · exact MergedCutProfiles.Batch010.valid420
  · exact MergedCutProfiles.Batch010.valid421
  · exact MergedCutProfiles.Batch010.valid422
  · exact MergedCutProfiles.Batch010.valid423
  · exact MergedCutProfiles.Batch010.valid424
  · exact MergedCutProfiles.Batch010.valid425
  · exact MergedCutProfiles.Batch010.valid426
  · exact MergedCutProfiles.Batch010.valid427
  · exact MergedCutProfiles.Batch010.valid428
  · exact MergedCutProfiles.Batch010.valid429
  · exact MergedCutProfiles.Batch010.valid430
  · exact MergedCutProfiles.Batch010.valid431
  · exact MergedCutProfiles.Batch010.valid432
  · exact MergedCutProfiles.Batch010.valid433
theorem numericValid57 : retention57.NumericValid := by decide +kernel
def certificate57 : RatCutBinCertificate := ⟨⟨retention57,(57828326918199667/31250000000000000),(4061079806220747/1000000000000000000),(3716556936614990061/500000000000000000),(545419571159664462953/125000000000000000),(222351007490559127/100000000000000000)⟩,(249894322084639273/250000000000000000),(274891807797778949/500000000000000000),(121319046874188127/1000000000000000000),(54536699628455047/1000000000000000000)⟩
theorem valid57 : certificate57.Valid := by decide +kernel
theorem sound57 : certificate57.Sound := rat_cut_bin_certificate_sound certificate57 profilesValid57 numericValid57 valid57

def retention58 : RatCutRetentionCertificate := ⟨(9/1000),(1/100),(316402637250000000/146096017909295143181),(619018969490984151/1000000000000000000),4,(144935358681245151231/64000000000000000000),true,MergedCutProfiles.Batch010.profile419,![MergedCutProfiles.Batch010.profile419,MergedCutProfiles.Batch010.profile421,MergedCutProfiles.Batch010.profile434,MergedCutProfiles.Batch010.profile425,MergedCutProfiles.Batch010.profile435,MergedCutProfiles.Batch010.profile436,MergedCutProfiles.Batch010.profile437,MergedCutProfiles.Batch010.profile438,MergedCutProfiles.Batch010.profile439,MergedCutProfiles.Batch011.profile440,MergedCutProfiles.Batch011.profile441,MergedCutProfiles.Batch011.profile442,MergedCutProfiles.Batch011.profile443,MergedCutProfiles.Batch011.profile444,MergedCutProfiles.Batch011.profile445,MergedCutProfiles.Batch011.profile446]⟩
theorem profilesValid58 : retention58.ProfilesValid := by
  change ∀ j : Fin 16, (retention58.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch010.valid419
  · exact MergedCutProfiles.Batch010.valid421
  · exact MergedCutProfiles.Batch010.valid434
  · exact MergedCutProfiles.Batch010.valid425
  · exact MergedCutProfiles.Batch010.valid435
  · exact MergedCutProfiles.Batch010.valid436
  · exact MergedCutProfiles.Batch010.valid437
  · exact MergedCutProfiles.Batch010.valid438
  · exact MergedCutProfiles.Batch010.valid439
  · exact MergedCutProfiles.Batch011.valid440
  · exact MergedCutProfiles.Batch011.valid441
  · exact MergedCutProfiles.Batch011.valid442
  · exact MergedCutProfiles.Batch011.valid443
  · exact MergedCutProfiles.Batch011.valid444
  · exact MergedCutProfiles.Batch011.valid445
  · exact MergedCutProfiles.Batch011.valid446
theorem numericValid58 : retention58.NumericValid := by decide +kernel
def certificate58 : RatCutBinCertificate := ⟨⟨retention58,(57828326918199667/31250000000000000),(4061079806220747/1000000000000000000),(3716556936614990061/500000000000000000),(545419571159664462953/125000000000000000),(1130285441501928437/500000000000000000)⟩,(249894322084639273/250000000000000000),(261729155907431813/500000000000000000),(34427052065781311/250000000000000000),(63331209733444347/1000000000000000000)⟩
theorem valid58 : certificate58.Valid := by decide +kernel
theorem sound58 : certificate58.Sound := rat_cut_bin_certificate_sound certificate58 profilesValid58 numericValid58 valid58

def retention59 : RatCutRetentionCertificate := ⟨(9/1000),(1/100),(1707985123847480615/584384071637180572724),(1265610549/1000000000),(12/5),(36587552730275593433/16000000000000000000),true,MergedCutProfiles.Batch011.profile447,![MergedCutProfiles.Batch011.profile447,MergedCutProfiles.Batch011.profile448,MergedCutProfiles.Batch010.profile425,MergedCutProfiles.Batch010.profile428,MergedCutProfiles.Batch011.profile449,MergedCutProfiles.Batch010.profile438,MergedCutProfiles.Batch011.profile450,MergedCutProfiles.Batch011.profile451,MergedCutProfiles.Batch011.profile452,MergedCutProfiles.Batch011.profile453,MergedCutProfiles.Batch011.profile454,MergedCutProfiles.Batch011.profile446,MergedCutProfiles.Batch011.profile455,MergedCutProfiles.Batch011.profile456,MergedCutProfiles.Batch011.profile457,MergedCutProfiles.Batch011.profile458]⟩
theorem profilesValid59 : retention59.ProfilesValid := by
  change ∀ j : Fin 16, (retention59.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch011.valid447
  · exact MergedCutProfiles.Batch011.valid448
  · exact MergedCutProfiles.Batch010.valid425
  · exact MergedCutProfiles.Batch010.valid428
  · exact MergedCutProfiles.Batch011.valid449
  · exact MergedCutProfiles.Batch010.valid438
  · exact MergedCutProfiles.Batch011.valid450
  · exact MergedCutProfiles.Batch011.valid451
  · exact MergedCutProfiles.Batch011.valid452
  · exact MergedCutProfiles.Batch011.valid453
  · exact MergedCutProfiles.Batch011.valid454
  · exact MergedCutProfiles.Batch011.valid446
  · exact MergedCutProfiles.Batch011.valid455
  · exact MergedCutProfiles.Batch011.valid456
  · exact MergedCutProfiles.Batch011.valid457
  · exact MergedCutProfiles.Batch011.valid458
theorem numericValid59 : retention59.NumericValid := by decide +kernel
def certificate59 : RatCutBinCertificate := ⟨⟨retention59,(57828326918199667/31250000000000000),(4061079806220747/1000000000000000000),(3716556936614990061/500000000000000000),(545419571159664462953/125000000000000000),(571073896994109057/250000000000000000)⟩,(249894322084639273/250000000000000000),(69286891934884057/200000000000000000),(143158617281258127/500000000000000000),(51848881377982139/250000000000000000)⟩
theorem valid59 : certificate59.Valid := by decide +kernel
theorem sound59 : certificate59.Sound := rat_cut_bin_certificate_sound certificate59 profilesValid59 numericValid59 valid59

def certificates : List RatCutBinCertificate := [certificate48,certificate49,certificate50,certificate51,certificate52,certificate53,certificate54,certificate55,certificate56,certificate57,certificate58,certificate59]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound48,List.forall_mem_cons.mpr ⟨sound49,List.forall_mem_cons.mpr ⟨sound50,List.forall_mem_cons.mpr ⟨sound51,List.forall_mem_cons.mpr ⟨sound52,List.forall_mem_cons.mpr ⟨sound53,List.forall_mem_cons.mpr ⟨sound54,List.forall_mem_cons.mpr ⟨sound55,List.forall_mem_cons.mpr ⟨sound56,List.forall_mem_cons.mpr ⟨sound57,List.forall_mem_cons.mpr ⟨sound58,List.forall_mem_cons.mpr ⟨sound59,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch004
