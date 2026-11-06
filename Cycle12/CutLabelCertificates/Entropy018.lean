import Cycle12.RationalLabelEntropy
import Cycle12.RationalMinorityBudget

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CutLabelCertificates.Entropy018

def certificate360 : RatLabelEntropyCertificate := ⟨(5041855942407029/1000000000000000000),⟨(1000000000000000000/5041855942407029),7,11,(5289981022142426869/1000000000000000000)⟩,⟨(1000000000000000000/994958144057592971),0,2,(50546089821307/10000000000000000)⟩,(6340089324701361/200000000000000000)⟩
theorem valid360 : certificate360.Valid := by decide +kernel
theorem sound360 : 0 ≤ cappedLabelEntropy (certificate360.rho:ℝ) ∧ cappedLabelEntropy (certificate360.rho:ℝ) ≤ (certificate360.bound:ℝ) := rat_label_entropy_certificate_sound certificate360 valid360

def certificate361 : RatLabelEntropyCertificate := ⟨(5436634183405621/1000000000000000000),⟨(1000000000000000000/5436634183405621),7,10,(651824390735490653/125000000000000000)⟩,⟨(1000000000000000000/994563365816594379),0,2,(545146646190219/100000000000000000)⟩,(33771674946986609/1000000000000000000)⟩
theorem valid361 : certificate361.Valid := by decide +kernel
theorem sound361 : 0 ≤ cappedLabelEntropy (certificate361.rho:ℝ) ∧ cappedLabelEntropy (certificate361.rho:ℝ) ≤ (certificate361.bound:ℝ) := rat_label_entropy_certificate_sound certificate361 valid361

def certificate362 : RatLabelEntropyCertificate := ⟨(47058445471961/8000000000000000),⟨(8000000000000000/47058445471961),7,9,(5135806470803361023/1000000000000000000)⟩,⟨(8000000000000000/7952941554528039),0,2,(1179934918075957/200000000000000000)⟩,(18037677248054313/500000000000000000)⟩
theorem valid362 : certificate362.Valid := by decide +kernel
theorem sound362 : 0 ≤ cappedLabelEntropy (certificate362.rho:ℝ) ∧ cappedLabelEntropy (certificate362.rho:ℝ) ≤ (certificate362.bound:ℝ) := rat_label_entropy_certificate_sound certificate362 valid362

def certificate363 : RatLabelEntropyCertificate := ⟨(1587870773960371/250000000000000000),⟨(250000000000000000/1587870773960371),7,8,(2529533467473910071/500000000000000000)⟩,⟨(250000000000000000/248412129226039629),0,3,(3185869791320911/500000000000000000)⟩,(38463847704443237/1000000000000000000)⟩
theorem valid363 : certificate363.Valid := by decide +kernel
theorem sound363 : 0 ≤ cappedLabelEntropy (certificate363.rho:ℝ) ∧ cappedLabelEntropy (certificate363.rho:ℝ) ≤ (certificate363.bound:ℝ) := rat_label_entropy_certificate_sound certificate363 valid363

def certificate364 : RatLabelEntropyCertificate := ⟨(1710225428304321/250000000000000000),⟨(250000000000000000/1710225428304321),7,6,(2492417863309340229/500000000000000000)⟩,⟨(250000000000000000/248289774571695679),0,3,(343220397261413/50000000000000000)⟩,(20459110233743991/500000000000000000)⟩
theorem valid364 : certificate364.Valid := by decide +kernel
theorem sound364 : 0 ≤ cappedLabelEntropy (certificate364.rho:ℝ) ∧ cappedLabelEntropy (certificate364.rho:ℝ) ≤ (certificate364.bound:ℝ) := rat_label_entropy_certificate_sound certificate364 valid364

def certificate365 : RatLabelEntropyCertificate := ⟨(7359941247071931/1000000000000000000),⟨(1000000000000000000/7359941247071931),7,5,(4911703329008006363/1000000000000000000)⟩,⟨(1000000000000000000/992640058752928069),0,3,(7387159245463653/1000000000000000000)⟩,(21741319055990409/500000000000000000)⟩
theorem valid365 : certificate365.Valid := by decide +kernel
theorem sound365 : 0 ≤ cappedLabelEntropy (certificate365.rho:ℝ) ∧ cappedLabelEntropy (certificate365.rho:ℝ) ≤ (certificate365.bound:ℝ) := rat_label_entropy_certificate_sound certificate365 valid365

def certificate366 : RatLabelEntropyCertificate := ⟨(783117422571211/100000000000000000),⟨(100000000000000000/783117422571211),6,15,(969928563050685831/200000000000000000)⟩,⟨(100000000000000000/99216882577428789),0,3,(982749863125951/125000000000000000)⟩,(22889414020271353/500000000000000000)⟩
theorem valid366 : certificate366.Valid := by decide +kernel
theorem sound366 : 0 ≤ cappedLabelEntropy (certificate366.rho:ℝ) ∧ cappedLabelEntropy (certificate366.rho:ℝ) ≤ (certificate366.bound:ℝ) := rat_label_entropy_certificate_sound certificate366 valid366

def certificate367 : RatLabelEntropyCertificate := ⟨(8381101019245803/1000000000000000000),⟨(1000000000000000000/8381101019245803),6,15,(2390887993286878147/500000000000000000)⟩,⟨(1000000000000000000/991618898980754197),0,3,(8416419925722509/1000000000000000000)⟩,(968448573099661/20000000000000000)⟩
theorem valid367 : certificate367.Valid := by decide +kernel
theorem sound367 : 0 ≤ cappedLabelEntropy (certificate367.rho:ℝ) ∧ cappedLabelEntropy (certificate367.rho:ℝ) ≤ (certificate367.bound:ℝ) := rat_label_entropy_certificate_sound certificate367 valid367

def certificate368 : RatLabelEntropyCertificate := ⟨(8950600193060389/1000000000000000000),⟨(1000000000000000000/8950600193060389),6,14,(4716034688266701301/1000000000000000000)⟩,⟨(1000000000000000000/991049399806939611),0,3,(4495448725807731/500000000000000000)⟩,(2044870580577147/40000000000000000)⟩
theorem valid368 : certificate368.Valid := by decide +kernel
theorem sound368 : 0 ≤ cappedLabelEntropy (certificate368.rho:ℝ) ∧ cappedLabelEntropy (certificate368.rho:ℝ) ≤ (certificate368.bound:ℝ) := rat_label_entropy_certificate_sound certificate368 valid368

def certificate369 : RatLabelEntropyCertificate := ⟨(9473233561575741/1000000000000000000),⟨(1000000000000000000/9473233561575741),6,12,(4659284976890122579/1000000000000000000)⟩,⟨(1000000000000000000/990526766438424259),0,3,(4759195025110531/500000000000000000)⟩,(535667149341663/10000000000000000)⟩
theorem valid369 : certificate369.Valid := by decide +kernel
theorem sound369 : 0 ≤ cappedLabelEntropy (certificate369.rho:ℝ) ∧ cappedLabelEntropy (certificate369.rho:ℝ) ≤ (certificate369.bound:ℝ) := rat_label_entropy_certificate_sound certificate369 valid369

def certificate370 : RatLabelEntropyCertificate := ⟨(2519981749611301/250000000000000000),⟨(250000000000000000/2519981749611301),6,11,(4597209258582877179/1000000000000000000)⟩,⟨(250000000000000000/247480018250388699),0,3,(10131073454557683/1000000000000000000)⟩,(56368486696811659/1000000000000000000)⟩
theorem valid370 : certificate370.Valid := by decide +kernel
theorem sound370 : 0 ≤ cappedLabelEntropy (certificate370.rho:ℝ) ∧ cappedLabelEntropy (certificate370.rho:ℝ) ≤ (certificate370.bound:ℝ) := rat_label_entropy_certificate_sound certificate370 valid370

def certificate371 : RatLabelEntropyCertificate := ⟨(10710441594864617/1000000000000000000),⟨(1000000000000000000/10710441594864617),6,10,(35441688776242131/7812500000000000)⟩,⟨(1000000000000000000/989289558405135383),0,3,(5384105618488603/500000000000000000)⟩,(29620592280045049/500000000000000000)⟩
theorem valid371 : certificate371.Valid := by decide +kernel
theorem sound371 : 0 ≤ cappedLabelEntropy (certificate371.rho:ℝ) ∧ cappedLabelEntropy (certificate371.rho:ℝ) ≤ (certificate371.bound:ℝ) := rat_label_entropy_certificate_sound certificate371 valid371

def certificate372 : RatLabelEntropyCertificate := ⟨(284135341019149/25000000000000000),⟨(25000000000000000/284135341019149),6,9,(1119295106580016873/250000000000000000)⟩,⟨(25000000000000000/24715864658980851),0,3,(11430493530840979/1000000000000000000)⟩,(15546397183303331/250000000000000000)⟩
theorem valid372 : certificate372.Valid := by decide +kernel
theorem sound372 : 0 ≤ cappedLabelEntropy (certificate372.rho:ℝ) ∧ cappedLabelEntropy (certificate372.rho:ℝ) ≤ (certificate372.bound:ℝ) := rat_label_entropy_certificate_sound certificate372 valid372

def certificate373 : RatLabelEntropyCertificate := ⟨(2393029731131419/200000000000000000),⟨(200000000000000000/2393029731131419),6,9,(442575713349028029/100000000000000000)⟩,⟨(200000000000000000/197606970268868581),0,3,(6018653608190769/500000000000000000)⟩,(12969624212433949/200000000000000000)⟩
theorem valid373 : certificate373.Valid := by decide +kernel
theorem sound373 : 0 ≤ cappedLabelEntropy (certificate373.rho:ℝ) ∧ cappedLabelEntropy (certificate373.rho:ℝ) ≤ (certificate373.bound:ℝ) := rat_label_entropy_certificate_sound certificate373 valid373

def certificate374 : RatLabelEntropyCertificate := ⟨(6330422656540923/500000000000000000),⟨(500000000000000000/6330422656540923),6,7,(4369241094109538051/1000000000000000000)⟩,⟨(500000000000000000/493669577343459077),0,3,(3185419200791911/250000000000000000)⟩,(67898642032214797/1000000000000000000)⟩
theorem valid374 : certificate374.Valid := by decide +kernel
theorem sound374 : 0 ≤ cappedLabelEntropy (certificate374.rho:ℝ) ∧ cappedLabelEntropy (certificate374.rho:ℝ) ≤ (certificate374.bound:ℝ) := rat_label_entropy_certificate_sound certificate374 valid374

def certificate375 : RatLabelEntropyCertificate := ⟨(13279145817559323/1000000000000000000),⟨(1000000000000000000/13279145817559323),6,7,(270097528623090613/62500000000000000)⟩,⟨(1000000000000000000/986720854182440677),0,3,(6684051030337939/500000000000000000)⟩,(1764430414122073/25000000000000000)⟩
theorem valid375 : certificate375.Valid := by decide +kernel
theorem sound375 : 0 ≤ cappedLabelEntropy (certificate375.rho:ℝ) ∧ cappedLabelEntropy (certificate375.rho:ℝ) ≤ (certificate375.bound:ℝ) := rat_label_entropy_certificate_sound certificate375 valid375

def certificate376 : RatLabelEntropyCertificate := ⟨(14016319432755097/1000000000000000000),⟨(1000000000000000000/14016319432755097),6,6,(2133766477234407321/500000000000000000)⟩,⟨(1000000000000000000/985983680567244903),0,3,(3528868916328063/250000000000000000)⟩,(36866366864542987/500000000000000000)⟩
theorem valid376 : certificate376.Valid := by decide +kernel
theorem sound376 : 0 ≤ cappedLabelEntropy (certificate376.rho:ℝ) ∧ cappedLabelEntropy (certificate376.rho:ℝ) ≤ (certificate376.bound:ℝ) := rat_label_entropy_certificate_sound certificate376 valid376

def certificate377 : RatLabelEntropyCertificate := ⟨(14681257380391671/1000000000000000000),⟨(1000000000000000000/14681257380391671),6,5,(527647950856063361/125000000000000000)⟩,⟨(1000000000000000000/985318742619608329),0,3,(14790093587994971/1000000000000000000)⟩,(4784077462461407/62500000000000000)⟩
theorem valid377 : certificate377.Valid := by decide +kernel
theorem sound377 : 0 ≤ cappedLabelEntropy (certificate377.rho:ℝ) ∧ cappedLabelEntropy (certificate377.rho:ℝ) ≤ (certificate377.bound:ℝ) := rat_label_entropy_certificate_sound certificate377 valid377

def certificate378 : RatLabelEntropyCertificate := ⟨(15462039086666689/1000000000000000000),⟨(1000000000000000000/15462039086666689),6,3,(4169367350169141511/1000000000000000000)⟩,⟨(1000000000000000000/984537960913333311),0,3,(7791411537566357/500000000000000000)⟩,(79808801790651587/1000000000000000000)⟩
theorem valid378 : certificate378.Valid := by decide +kernel
theorem sound378 : 0 ≤ cappedLabelEntropy (certificate378.rho:ℝ) ∧ cappedLabelEntropy (certificate378.rho:ℝ) ≤ (certificate378.bound:ℝ) := rat_label_entropy_certificate_sound certificate378 valid378

def certificate379 : RatLabelEntropyCertificate := ⟨(3230917682053887/200000000000000000),⟨(200000000000000000/3230917682053887),5,16,(412555115757468209/100000000000000000)⟩,⟨(200000000000000000/196769082317946113),0,3,(4071624078664739/250000000000000000)⟩,(41334987793089941/500000000000000000)⟩
theorem valid379 : certificate379.Valid := by decide +kernel
theorem sound379 : 0 ≤ cappedLabelEntropy (certificate379.rho:ℝ) ∧ cappedLabelEntropy (certificate379.rho:ℝ) ≤ (certificate379.bound:ℝ) := rat_label_entropy_certificate_sound certificate379 valid379

end Cycle12.CutLabelCertificates.Entropy018
