import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch429
import Cycle12.MergedCutProfiles.Batch430
import Cycle12.MergedCutProfiles.Batch549
import Cycle12.MergedCutProfiles.Batch550
import Cycle12.MergedCutProfiles.Batch551
import Cycle12.MergedCutProfiles.Batch552
import Cycle12.MergedCutProfiles.Batch637
import Cycle12.MergedCutProfiles.Batch638
import Cycle12.MergedCutProfiles.Batch639

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch355

def retention4260 : RatCutRetentionCertificate := ⟨(13/200),(131/2000),(565971302500000000/101248192732383573129),(166061723920296861/200000000000000000),(17/5),(602484554078238327241/256000000000000000000),true,MergedCutProfiles.Batch637.profile25512,![MergedCutProfiles.Batch637.profile25512,MergedCutProfiles.Batch637.profile25513,MergedCutProfiles.Batch637.profile25514,MergedCutProfiles.Batch637.profile25515,MergedCutProfiles.Batch637.profile25516,MergedCutProfiles.Batch637.profile25517,MergedCutProfiles.Batch637.profile25518,MergedCutProfiles.Batch637.profile25508,MergedCutProfiles.Batch550.profile22033,MergedCutProfiles.Batch549.profile21994,MergedCutProfiles.Batch637.profile25511,MergedCutProfiles.Batch637.profile25519,MergedCutProfiles.Batch638.profile25520,MergedCutProfiles.Batch638.profile25521,MergedCutProfiles.Batch638.profile25522,MergedCutProfiles.Batch638.profile25523]⟩
theorem profilesValid4260 : retention4260.ProfilesValid := by
  change ∀ j : Fin 16, (retention4260.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch637.valid25512
  · exact MergedCutProfiles.Batch637.valid25513
  · exact MergedCutProfiles.Batch637.valid25514
  · exact MergedCutProfiles.Batch637.valid25515
  · exact MergedCutProfiles.Batch637.valid25516
  · exact MergedCutProfiles.Batch637.valid25517
  · exact MergedCutProfiles.Batch637.valid25518
  · exact MergedCutProfiles.Batch637.valid25508
  · exact MergedCutProfiles.Batch550.valid22033
  · exact MergedCutProfiles.Batch549.valid21994
  · exact MergedCutProfiles.Batch637.valid25511
  · exact MergedCutProfiles.Batch637.valid25519
  · exact MergedCutProfiles.Batch638.valid25520
  · exact MergedCutProfiles.Batch638.valid25521
  · exact MergedCutProfiles.Batch638.valid25522
  · exact MergedCutProfiles.Batch638.valid25523
theorem numericValid4260 : retention4260.NumericValid := by decide +kernel
def certificate4260 : RatCutBinCertificate := ⟨⟨retention4260,(1072522650376235353/500000000000000000),(225107070921290071/1000000000000000000),(4356874495286830139/250000000000000000),(3540212236440684184697/1000000000000000000),(2259249137700044397/1000000000000000000)⟩,(999527907409721401/1000000000000000000),(3113925015298783/7812500000000000),(234783751061575331/1000000000000000000),(63106636859655343/500000000000000000)⟩
theorem valid4260 : certificate4260.Valid := by decide +kernel
theorem sound4260 : certificate4260.Sound := rat_cut_bin_certificate_sound certificate4260 profilesValid4260 numericValid4260 valid4260

def retention4261 : RatCutRetentionCertificate := ⟨(13/200),(131/2000),(1617229258516876157/202496385464767146258),(226388521/200000000),(53/20),(37137772314217837373/16000000000000000000),true,MergedCutProfiles.Batch638.profile25524,![MergedCutProfiles.Batch638.profile25524,MergedCutProfiles.Batch638.profile25525,MergedCutProfiles.Batch638.profile25526,MergedCutProfiles.Batch638.profile25527,MergedCutProfiles.Batch638.profile25528,MergedCutProfiles.Batch638.profile25529,MergedCutProfiles.Batch549.profile21994,MergedCutProfiles.Batch638.profile25530,MergedCutProfiles.Batch638.profile25531,MergedCutProfiles.Batch638.profile25532,MergedCutProfiles.Batch550.profile22024,MergedCutProfiles.Batch638.profile25533,MergedCutProfiles.Batch638.profile25534,MergedCutProfiles.Batch549.profile21997,MergedCutProfiles.Batch638.profile25535,MergedCutProfiles.Batch638.profile25536]⟩
theorem profilesValid4261 : retention4261.ProfilesValid := by
  change ∀ j : Fin 16, (retention4261.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch638.valid25524
  · exact MergedCutProfiles.Batch638.valid25525
  · exact MergedCutProfiles.Batch638.valid25526
  · exact MergedCutProfiles.Batch638.valid25527
  · exact MergedCutProfiles.Batch638.valid25528
  · exact MergedCutProfiles.Batch638.valid25529
  · exact MergedCutProfiles.Batch549.valid21994
  · exact MergedCutProfiles.Batch638.valid25530
  · exact MergedCutProfiles.Batch638.valid25531
  · exact MergedCutProfiles.Batch638.valid25532
  · exact MergedCutProfiles.Batch550.valid22024
  · exact MergedCutProfiles.Batch638.valid25533
  · exact MergedCutProfiles.Batch638.valid25534
  · exact MergedCutProfiles.Batch549.valid21997
  · exact MergedCutProfiles.Batch638.valid25535
  · exact MergedCutProfiles.Batch638.valid25536
theorem numericValid4261 : retention4261.NumericValid := by decide +kernel
def certificate4261 : RatCutBinCertificate := ⟨⟨retention4261,(1072522650376235353/500000000000000000),(225107070921290071/1000000000000000000),(4356874495286830139/250000000000000000),(3540212236440684184697/1000000000000000000),(1123842742042019013/500000000000000000)⟩,(999527907409721401/1000000000000000000),(171765141119880401/500000000000000000),(144703750397177131/500000000000000000),(191253583861951109/1000000000000000000)⟩
theorem valid4261 : certificate4261.Valid := by decide +kernel
theorem sound4261 : certificate4261.Sound := rat_cut_bin_certificate_sound certificate4261 profilesValid4261 numericValid4261 valid4261

def retention4262 : RatCutRetentionCertificate := ⟨(13/200),(131/2000),(22591009712289327031/202496385464767146258),(1617229258516876157/1000000000000000000),2,(483283475258813485789/256000000000000000000),true,MergedCutProfiles.Batch549.profile21997,![MergedCutProfiles.Batch549.profile21997,MergedCutProfiles.Batch638.profile25537,MergedCutProfiles.Batch638.profile25538,MergedCutProfiles.Batch638.profile25539,MergedCutProfiles.Batch638.profile25540,MergedCutProfiles.Batch638.profile25541,MergedCutProfiles.Batch638.profile25542,MergedCutProfiles.Batch638.profile25543,MergedCutProfiles.Batch638.profile25544,MergedCutProfiles.Batch638.profile25545,MergedCutProfiles.Batch638.profile25546,MergedCutProfiles.Batch638.profile25547,MergedCutProfiles.Batch638.profile25548,MergedCutProfiles.Batch638.profile25549,MergedCutProfiles.Batch638.profile25550,MergedCutProfiles.Batch638.profile25551]⟩
theorem profilesValid4262 : retention4262.ProfilesValid := by
  change ∀ j : Fin 16, (retention4262.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch549.valid21997
  · exact MergedCutProfiles.Batch638.valid25537
  · exact MergedCutProfiles.Batch638.valid25538
  · exact MergedCutProfiles.Batch638.valid25539
  · exact MergedCutProfiles.Batch638.valid25540
  · exact MergedCutProfiles.Batch638.valid25541
  · exact MergedCutProfiles.Batch638.valid25542
  · exact MergedCutProfiles.Batch638.valid25543
  · exact MergedCutProfiles.Batch638.valid25544
  · exact MergedCutProfiles.Batch638.valid25545
  · exact MergedCutProfiles.Batch638.valid25546
  · exact MergedCutProfiles.Batch638.valid25547
  · exact MergedCutProfiles.Batch638.valid25548
  · exact MergedCutProfiles.Batch638.valid25549
  · exact MergedCutProfiles.Batch638.valid25550
  · exact MergedCutProfiles.Batch638.valid25551
theorem numericValid4262 : retention4262.NumericValid := by decide +kernel
def certificate4262 : RatCutBinCertificate := ⟨⟨retention4262,(1072522650376235353/500000000000000000),(225107070921290071/1000000000000000000),(4356874495286830139/250000000000000000),(3540212236440684184697/1000000000000000000),(1832410850653118419/1000000000000000000)⟩,(999527907409721401/1000000000000000000),(181763374845194003/500000000000000000),(268615713102146071/1000000000000000000),(191675669827156763/1000000000000000000)⟩
theorem valid4262 : certificate4262.Valid := by decide +kernel
theorem sound4262 : certificate4262.Sound := rat_cut_bin_certificate_sound certificate4262 profilesValid4262 numericValid4262 valid4262

def retention4263 : RatCutRetentionCertificate := ⟨(13/200),(131/2000),(32000000000000000000/101248192732383573129),(22591009712289327031/1000000000000000000),1,(123243302338153125422653094910870350803/90364038849157308124000000000000000000),false,MergedCutProfiles.Batch638.profile25552,(fun _ => MergedCutProfiles.Batch638.profile25552)⟩
theorem profilesValid4263 : retention4263.ProfilesValid := by
  exact MergedCutProfiles.Batch638.valid25552
theorem numericValid4263 : retention4263.NumericValid := by decide +kernel
def certificate4263 : RatCutBinCertificate := ⟨⟨retention4263,(1072522650376235353/500000000000000000),(225107070921290071/1000000000000000000),(4356874495286830139/250000000000000000),(3540212236440684184697/1000000000000000000),(41754570698086743/31250000000000000)⟩,(999527907409721401/1000000000000000000),(81679750048454597/250000000000000000),(307784081645840687/1000000000000000000),(388090809637057253/1000000000000000000)⟩
theorem valid4263 : certificate4263.Valid := by decide +kernel
theorem sound4263 : certificate4263.Sound := rat_cut_bin_certificate_sound certificate4263 profilesValid4263 numericValid4263 valid4263

def retention4264 : RatCutRetentionCertificate := ⟨(13/200),(131/2000),(1/2),64,1,(63854086730460624674666153654156798599/64000000000000000000000000000000000000),false,MergedCutProfiles.Batch429.profile17180,(fun _ => MergedCutProfiles.Batch429.profile17180)⟩
theorem profilesValid4264 : retention4264.ProfilesValid := by
  exact MergedCutProfiles.Batch429.valid17180
theorem numericValid4264 : retention4264.NumericValid := by decide +kernel
def certificate4264 : RatCutBinCertificate := ⟨⟨retention4264,(1072522650376235353/500000000000000000),(225107070921290071/1000000000000000000),(4356874495286830139/250000000000000000),(3540212236440684184697/1000000000000000000),(485006505018335303/500000000000000000)⟩,(999527907409721401/1000000000000000000),(219115839729983799/500000000000000000),(200223463651949897/1000000000000000000),(95614148989756523/500000000000000000)⟩
theorem valid4264 : certificate4264.Valid := by decide +kernel
theorem sound4264 : certificate4264.Sound := rat_cut_bin_certificate_sound certificate4264 profilesValid4264 numericValid4264 valid4264

def retention4265 : RatCutRetentionCertificate := ⟨(13/200),(131/2000),(32000000000000000000/101248192732383573129),(23013161769427137349/1000000000000000000),1,(125582166108180417566278075875537231979/92052647077708549396000000000000000000),false,MergedCutProfiles.Batch638.profile25552,(fun _ => MergedCutProfiles.Batch638.profile25552)⟩
theorem profilesValid4265 : retention4265.ProfilesValid := by
  exact MergedCutProfiles.Batch638.valid25552
theorem numericValid4265 : retention4265.NumericValid := by decide +kernel
def certificate4265 : RatCutBinCertificate := ⟨⟨retention4265,(975822383376235353/500000000000000000),(225107070921290071/1000000000000000000),(4356874495286830139/250000000000000000),(3540212236440684184697/1000000000000000000),(1339033829466090989/1000000000000000000)⟩,(499785238589114461/500000000000000000),(9332880386923013/250000000000000000),(164647253334275981/200000000000000000),(130158180989509701/125000000000000000)⟩
theorem valid4265 : certificate4265.Valid := by decide +kernel
theorem sound4265 : certificate4265.Sound := rat_cut_bin_certificate_sound certificate4265 profilesValid4265 numericValid4265 valid4265

def retention4266 : RatCutRetentionCertificate := ⟨(13/200),(131/2000),(1/2),64,1,(63854086730460624674666153654156798599/64000000000000000000000000000000000000),false,MergedCutProfiles.Batch429.profile17180,(fun _ => MergedCutProfiles.Batch429.profile17180)⟩
theorem profilesValid4266 : retention4266.ProfilesValid := by
  exact MergedCutProfiles.Batch429.valid17180
theorem numericValid4266 : retention4266.NumericValid := by decide +kernel
def certificate4266 : RatCutBinCertificate := ⟨⟨retention4266,(975822383376235353/500000000000000000),(225107070921290071/1000000000000000000),(4356874495286830139/250000000000000000),(3540212236440684184697/1000000000000000000),(972511123708781701/1000000000000000000)⟩,(499785238589114461/500000000000000000),(25700564774604537/500000000000000000),(784620182506386477/1000000000000000000),(751303619522072883/1000000000000000000)⟩
theorem valid4266 : certificate4266.Valid := by decide +kernel
theorem sound4266 : certificate4266.Sound := rat_cut_bin_certificate_sound certificate4266 profilesValid4266 numericValid4266 valid4266

def retention4267 : RatCutRetentionCertificate := ⟨(131/2000),(33/500),(838515079824390462/198806338180814466443),(33208518012847147/40000000000000000),(17/5),(37869416635073844223/16000000000000000000),true,MergedCutProfiles.Batch638.profile25553,![MergedCutProfiles.Batch638.profile25553,MergedCutProfiles.Batch638.profile25554,MergedCutProfiles.Batch638.profile25555,MergedCutProfiles.Batch638.profile25556,MergedCutProfiles.Batch638.profile25557,MergedCutProfiles.Batch638.profile25558,MergedCutProfiles.Batch638.profile25559,MergedCutProfiles.Batch639.profile25560,MergedCutProfiles.Batch551.profile22053,MergedCutProfiles.Batch639.profile25561,MergedCutProfiles.Batch639.profile25562,MergedCutProfiles.Batch639.profile25563,MergedCutProfiles.Batch639.profile25564,MergedCutProfiles.Batch639.profile25565,MergedCutProfiles.Batch639.profile25566,MergedCutProfiles.Batch639.profile25567]⟩
theorem profilesValid4267 : retention4267.ProfilesValid := by
  change ∀ j : Fin 16, (retention4267.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch638.valid25553
  · exact MergedCutProfiles.Batch638.valid25554
  · exact MergedCutProfiles.Batch638.valid25555
  · exact MergedCutProfiles.Batch638.valid25556
  · exact MergedCutProfiles.Batch638.valid25557
  · exact MergedCutProfiles.Batch638.valid25558
  · exact MergedCutProfiles.Batch638.valid25559
  · exact MergedCutProfiles.Batch639.valid25560
  · exact MergedCutProfiles.Batch551.valid22053
  · exact MergedCutProfiles.Batch639.valid25561
  · exact MergedCutProfiles.Batch639.valid25562
  · exact MergedCutProfiles.Batch639.valid25563
  · exact MergedCutProfiles.Batch639.valid25564
  · exact MergedCutProfiles.Batch639.valid25565
  · exact MergedCutProfiles.Batch639.valid25566
  · exact MergedCutProfiles.Batch639.valid25567
theorem numericValid4267 : retention4267.NumericValid := by decide +kernel
def certificate4267 : RatCutBinCertificate := ⟨⟨retention4267,(215303782971840637/100000000000000000),(229314578619222081/1000000000000000000),(879802960495445129/50000000000000000),(1754677969578086812537/500000000000000000),(113571833543114213/50000000000000000)⟩,(999524526734776649/1000000000000000000),(389959153160996587/1000000000000000000),(242809315214993467/1000000000000000000),(131093501770020061/1000000000000000000)⟩
theorem valid4267 : certificate4267.Valid := by decide +kernel
theorem sound4267 : certificate4267.Sound := rat_cut_bin_certificate_sound certificate4267 profilesValid4267 numericValid4267 valid4267

def retention4268 : RatCutRetentionCertificate := ⟨(131/2000),(33/500),(67316350000000000/11694490481224380379),(419257539912195231/500000000000000000),(67/20),(5871115532463626217/2500000000000000000),true,MergedCutProfiles.Batch639.profile25568,![MergedCutProfiles.Batch639.profile25568,MergedCutProfiles.Batch639.profile25569,MergedCutProfiles.Batch639.profile25570,MergedCutProfiles.Batch639.profile25571,MergedCutProfiles.Batch639.profile25572,MergedCutProfiles.Batch639.profile25573,MergedCutProfiles.Batch639.profile25574,MergedCutProfiles.Batch639.profile25575,MergedCutProfiles.Batch430.profile17216,MergedCutProfiles.Batch551.profile22054,MergedCutProfiles.Batch639.profile25566,MergedCutProfiles.Batch639.profile25576,MergedCutProfiles.Batch430.profile17231,MergedCutProfiles.Batch639.profile25577,MergedCutProfiles.Batch639.profile25578,MergedCutProfiles.Batch639.profile25579]⟩
theorem profilesValid4268 : retention4268.ProfilesValid := by
  change ∀ j : Fin 16, (retention4268.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch639.valid25568
  · exact MergedCutProfiles.Batch639.valid25569
  · exact MergedCutProfiles.Batch639.valid25570
  · exact MergedCutProfiles.Batch639.valid25571
  · exact MergedCutProfiles.Batch639.valid25572
  · exact MergedCutProfiles.Batch639.valid25573
  · exact MergedCutProfiles.Batch639.valid25574
  · exact MergedCutProfiles.Batch639.valid25575
  · exact MergedCutProfiles.Batch430.valid17216
  · exact MergedCutProfiles.Batch551.valid22054
  · exact MergedCutProfiles.Batch639.valid25566
  · exact MergedCutProfiles.Batch639.valid25576
  · exact MergedCutProfiles.Batch430.valid17231
  · exact MergedCutProfiles.Batch639.valid25577
  · exact MergedCutProfiles.Batch639.valid25578
  · exact MergedCutProfiles.Batch639.valid25579
theorem numericValid4268 : retention4268.NumericValid := by decide +kernel
def certificate4268 : RatCutBinCertificate := ⟨⟨retention4268,(215303782971840637/100000000000000000),(229314578619222081/1000000000000000000),(879802960495445129/50000000000000000),(1754677969578086812537/500000000000000000),(2254447302203637529/1000000000000000000)⟩,(999524526734776649/1000000000000000000),(390823141659956861/1000000000000000000),(241996688531116693/1000000000000000000),(131305226308863407/1000000000000000000)⟩
theorem valid4268 : certificate4268.Valid := by decide +kernel
theorem sound4268 : certificate4268.Sound := rat_cut_bin_certificate_sound certificate4268 profilesValid4268 numericValid4268 valid4268

def retention4269 : RatCutRetentionCertificate := ⟨(131/2000),(33/500),(1973099664149363372/198806338180814466443),(22887559/20000000),(13/5),(18418369538133026969/8000000000000000000),true,MergedCutProfiles.Batch639.profile25580,![MergedCutProfiles.Batch639.profile25580,MergedCutProfiles.Batch639.profile25581,MergedCutProfiles.Batch639.profile25582,MergedCutProfiles.Batch639.profile25574,MergedCutProfiles.Batch639.profile25583,MergedCutProfiles.Batch639.profile25565,MergedCutProfiles.Batch639.profile25576,MergedCutProfiles.Batch639.profile25584,MergedCutProfiles.Batch552.profile22084,MergedCutProfiles.Batch639.profile25585,MergedCutProfiles.Batch639.profile25586,MergedCutProfiles.Batch639.profile25587,MergedCutProfiles.Batch639.profile25588,MergedCutProfiles.Batch639.profile25589,MergedCutProfiles.Batch430.profile17202,MergedCutProfiles.Batch639.profile25590]⟩
theorem profilesValid4269 : retention4269.ProfilesValid := by
  change ∀ j : Fin 16, (retention4269.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch639.valid25580
  · exact MergedCutProfiles.Batch639.valid25581
  · exact MergedCutProfiles.Batch639.valid25582
  · exact MergedCutProfiles.Batch639.valid25574
  · exact MergedCutProfiles.Batch639.valid25583
  · exact MergedCutProfiles.Batch639.valid25565
  · exact MergedCutProfiles.Batch639.valid25576
  · exact MergedCutProfiles.Batch639.valid25584
  · exact MergedCutProfiles.Batch552.valid22084
  · exact MergedCutProfiles.Batch639.valid25585
  · exact MergedCutProfiles.Batch639.valid25586
  · exact MergedCutProfiles.Batch639.valid25587
  · exact MergedCutProfiles.Batch639.valid25588
  · exact MergedCutProfiles.Batch639.valid25589
  · exact MergedCutProfiles.Batch430.valid17202
  · exact MergedCutProfiles.Batch639.valid25590
theorem numericValid4269 : retention4269.NumericValid := by decide +kernel
def certificate4269 : RatCutBinCertificate := ⟨⟨retention4269,(215303782971840637/100000000000000000),(229314578619222081/1000000000000000000),(879802960495445129/50000000000000000),(1754677969578086812537/500000000000000000),(445868381726482849/200000000000000000)⟩,(999524526734776649/1000000000000000000),(67829594656569979/200000000000000000),(294117069671419501/1000000000000000000),(97829877746472909/500000000000000000)⟩
theorem valid4269 : certificate4269.Valid := by decide +kernel
theorem sound4269 : certificate4269.Sound := rat_cut_bin_certificate_sound certificate4269 profilesValid4269 numericValid4269 valid4269

def retention4270 : RatCutRetentionCertificate := ⟨(131/2000),(33/500),(34996615483567902411/198806338180814466443),(493274916037340843/250000000000000000),(7/4),(13502345501728348852883282849666147599/7892398656597453488000000000000000000),false,MergedCutProfiles.Batch639.profile25591,(fun _ => MergedCutProfiles.Batch639.profile25591)⟩
theorem profilesValid4270 : retention4270.ProfilesValid := by
  exact MergedCutProfiles.Batch639.valid25591
theorem numericValid4270 : retention4270.NumericValid := by decide +kernel
def certificate4270 : RatCutBinCertificate := ⟨⟨retention4270,(215303782971840637/100000000000000000),(229314578619222081/1000000000000000000),(879802960495445129/50000000000000000),(1754677969578086812537/500000000000000000),(830850045154668833/500000000000000000)⟩,(999524526734776649/1000000000000000000),(368376068578631083/1000000000000000000),(131870696794120721/500000000000000000),(196310129380067943/1000000000000000000)⟩
theorem valid4270 : certificate4270.Valid := by decide +kernel
theorem sound4270 : certificate4270.Sound := rat_cut_bin_certificate_sound certificate4270 profilesValid4270 numericValid4270 valid4270

def retention4271 : RatCutRetentionCertificate := ⟨(131/2000),(33/500),(64000000000000000000/198806338180814466443),(34996615483567902411/1000000000000000000),1,(190219588411104541095786471241799050283/139986461934271609644000000000000000000),false,MergedCutProfiles.Batch639.profile25592,(fun _ => MergedCutProfiles.Batch639.profile25592)⟩
theorem profilesValid4271 : retention4271.ProfilesValid := by
  exact MergedCutProfiles.Batch639.valid25592
theorem numericValid4271 : retention4271.NumericValid := by decide +kernel
def certificate4271 : RatCutBinCertificate := ⟨⟨retention4271,(215303782971840637/100000000000000000),(229314578619222081/1000000000000000000),(879802960495445129/50000000000000000),(1754677969578086812537/500000000000000000),(1330783970486949901/1000000000000000000)⟩,(999524526734776649/1000000000000000000),(319032031253188823/1000000000000000000),(31647167713257273/100000000000000000),(405530396396570247/1000000000000000000)⟩
theorem valid4271 : certificate4271.Valid := by decide +kernel
theorem sound4271 : certificate4271.Sound := rat_cut_bin_certificate_sound certificate4271 profilesValid4271 numericValid4271 valid4271

def certificates : List RatCutBinCertificate := [certificate4260,certificate4261,certificate4262,certificate4263,certificate4264,certificate4265,certificate4266,certificate4267,certificate4268,certificate4269,certificate4270,certificate4271]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound4260,List.forall_mem_cons.mpr ⟨sound4261,List.forall_mem_cons.mpr ⟨sound4262,List.forall_mem_cons.mpr ⟨sound4263,List.forall_mem_cons.mpr ⟨sound4264,List.forall_mem_cons.mpr ⟨sound4265,List.forall_mem_cons.mpr ⟨sound4266,List.forall_mem_cons.mpr ⟨sound4267,List.forall_mem_cons.mpr ⟨sound4268,List.forall_mem_cons.mpr ⟨sound4269,List.forall_mem_cons.mpr ⟨sound4270,List.forall_mem_cons.mpr ⟨sound4271,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch355
