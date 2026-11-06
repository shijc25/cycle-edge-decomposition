import Cycle12.RationalLabelEntropy
import Cycle12.RationalMinorityBudget

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CutLabelCertificates.Entropy020

def certificate400 : RatLabelEntropyCertificate := ⟨(30516418325573063/1000000000000000000),⟨(1000000000000000000/30516418325573063),5,3,(1744745217223423229/500000000000000000)⟩,⟨(1000000000000000000/969483581674426937),0,4,(6198347856192553/200000000000000000)⟩,(27306546448218693/200000000000000000)⟩
theorem valid400 : certificate400.Valid := by decide +kernel
theorem sound400 : 0 ≤ cappedLabelEntropy (certificate400.rho:ℝ) ∧ cappedLabelEntropy (certificate400.rho:ℝ) ≤ (certificate400.bound:ℝ) := rat_label_entropy_certificate_sound certificate400 valid400

def certificate401 : RatLabelEntropyCertificate := ⟨(15562791199386269/500000000000000000),⟨(500000000000000000/15562791199386269),5,2,(54214456449455867/15625000000000000)⟩,⟨(500000000000000000/484437208800613731),0,4,(31620275488909591/1000000000000000000)⟩,(69316647004864347/500000000000000000)⟩
theorem valid401 : certificate401.Valid := by decide +kernel
theorem sound401 : 0 ≤ cappedLabelEntropy (certificate401.rho:ℝ) ∧ cappedLabelEntropy (certificate401.rho:ℝ) ≤ (certificate401.bound:ℝ) := rat_label_entropy_certificate_sound certificate401 valid401

def certificate402 : RatLabelEntropyCertificate := ⟨(15733299768234913/500000000000000000),⟨(500000000000000000/15733299768234913),4,15,(691765725575193397/200000000000000000)⟩,⟨(500000000000000000/484266700231765087),0,4,(3197230993208607/100000000000000000)⟩,(17475478169730961/125000000000000000)⟩
theorem valid402 : certificate402.Valid := by decide +kernel
theorem sound402 : 0 ≤ cappedLabelEntropy (certificate402.rho:ℝ) ∧ cappedLabelEntropy (certificate402.rho:ℝ) ≤ (certificate402.bound:ℝ) := rat_label_entropy_certificate_sound certificate402 valid402

def certificate403 : RatLabelEntropyCertificate := ⟨(16033523349843003/500000000000000000),⟨(500000000000000000/16033523349843003),4,15,(3439926358707253093/1000000000000000000)⟩,⟨(500000000000000000/483966476650156997),0,4,(32592457223871001/1000000000000000000)⟩,(35463898141040483/250000000000000000)⟩
theorem valid403 : certificate403.Valid := by decide +kernel
theorem sound403 : 0 ≤ cappedLabelEntropy (certificate403.rho:ℝ) ∧ cappedLabelEntropy (certificate403.rho:ℝ) ≤ (certificate403.bound:ℝ) := rat_label_entropy_certificate_sound certificate403 valid403

def certificate404 : RatLabelEntropyCertificate := ⟨(32691795390576027/1000000000000000000),⟨(1000000000000000000/32691795390576027),4,15,(684126227609589763/200000000000000000)⟩,⟨(1000000000000000000/967308204609423973),0,4,(33238111859769773/1000000000000000000)⟩,(17997258947422233/125000000000000000)⟩
theorem valid404 : certificate404.Valid := by decide +kernel
theorem sound404 : 0 ≤ cappedLabelEntropy (certificate404.rho:ℝ) ∧ cappedLabelEntropy (certificate404.rho:ℝ) ≤ (certificate404.bound:ℝ) := rat_label_entropy_certificate_sound certificate404 valid404

def certificate405 : RatLabelEntropyCertificate := ⟨(33672670702528971/1000000000000000000),⟨(1000000000000000000/33672670702528971),4,14,(3391068729010384003/1000000000000000000)⟩,⟨(1000000000000000000/966327329297471029),0,4,(4281581495245331/125000000000000000)⟩,(147285614333369259/1000000000000000000)⟩
theorem valid405 : certificate405.Valid := by decide +kernel
theorem sound405 : 0 ≤ cappedLabelEntropy (certificate405.rho:ℝ) ∧ cappedLabelEntropy (certificate405.rho:ℝ) ≤ (certificate405.bound:ℝ) := rat_label_entropy_certificate_sound certificate405 valid405

def certificate406 : RatLabelEntropyCertificate := ⟨(34294864757325913/1000000000000000000),⟨(1000000000000000000/34294864757325913),4,15,(1686379825774294131/500000000000000000)⟩,⟨(1000000000000000000/965705135242674087),0,4,(17448367192879073/500000000000000000)⟩,(4667759115885961/31250000000000000)⟩
theorem valid406 : certificate406.Valid := by decide +kernel
theorem sound406 : 0 ≤ cappedLabelEntropy (certificate406.rho:ℝ) ∧ cappedLabelEntropy (certificate406.rho:ℝ) ≤ (certificate406.bound:ℝ) := rat_label_entropy_certificate_sound certificate406 valid406

def certificate407 : RatLabelEntropyCertificate := ⟨(17462593519345381/500000000000000000),⟨(500000000000000000/17462593519345381),4,13,(670909403682983787/200000000000000000)⟩,⟨(500000000000000000/482537406480654619),0,4,(35549654263389571/1000000000000000000)⟩,(18933282248412921/125000000000000000)⟩
theorem valid407 : certificate407.Valid := by decide +kernel
theorem sound407 : 0 ≤ cappedLabelEntropy (certificate407.rho:ℝ) ∧ cappedLabelEntropy (certificate407.rho:ℝ) ≤ (certificate407.bound:ℝ) := rat_label_entropy_certificate_sound certificate407 valid407

def certificate408 : RatLabelEntropyCertificate := ⟨(17634691016274993/500000000000000000),⟨(500000000000000000/17634691016274993),4,13,(3344740055938140041/1000000000000000000)⟩,⟨(500000000000000000/482365308983725007),0,4,(17953184489381017/500000000000000000)⟩,(76303444183151623/500000000000000000)⟩
theorem valid408 : certificate408.Valid := by decide +kernel
theorem sound408 : 0 ≤ cappedLabelEntropy (certificate408.rho:ℝ) ∧ cappedLabelEntropy (certificate408.rho:ℝ) ≤ (certificate408.bound:ℝ) := rat_label_entropy_certificate_sound certificate408 valid408

def certificate409 : RatLabelEntropyCertificate := ⟨(35930067472794033/1000000000000000000),⟨(1000000000000000000/35930067472794033),4,13,(415772599995341287/125000000000000000)⟩,⟨(1000000000000000000/964069932527205967),0,4,(36591442887429637/1000000000000000000)⟩,(154786610444930333/1000000000000000000)⟩
theorem valid409 : certificate409.Valid := by decide +kernel
theorem sound409 : 0 ≤ cappedLabelEntropy (certificate409.rho:ℝ) ∧ cappedLabelEntropy (certificate409.rho:ℝ) ≤ (certificate409.bound:ℝ) := rat_label_entropy_certificate_sound certificate409 valid409

def certificate410 : RatLabelEntropyCertificate := ⟨(36571936194153781/1000000000000000000),⟨(1000000000000000000/36571936194153781),4,13,(3308474103345326029/1000000000000000000)⟩,⟨(1000000000000000000/963428063805846219),0,4,(18628727623906517/500000000000000000)⟩,(78446090889644441/500000000000000000)⟩
theorem valid410 : certificate410.Valid := by decide +kernel
theorem sound410 : 0 ≤ cappedLabelEntropy (certificate410.rho:ℝ) ∧ cappedLabelEntropy (certificate410.rho:ℝ) ≤ (certificate410.bound:ℝ) := rat_label_entropy_certificate_sound certificate410 valid410

def certificate411 : RatLabelEntropyCertificate := ⟨(37251390587961293/1000000000000000000),⟨(1000000000000000000/37251390587961293),4,12,(3290066003632923803/1000000000000000000)⟩,⟨(1000000000000000000/962748609412038707),0,4,(37962950679708311/1000000000000000000)⟩,(15910831173756991/100000000000000000)⟩
theorem valid411 : certificate411.Valid := by decide +kernel
theorem sound411 : 0 ≤ cappedLabelEntropy (certificate411.rho:ℝ) ∧ cappedLabelEntropy (certificate411.rho:ℝ) ≤ (certificate411.bound:ℝ) := rat_label_entropy_certificate_sound certificate411 valid411

def certificate412 : RatLabelEntropyCertificate := ⟨(7518763520299381/200000000000000000),⟨(200000000000000000/7518763520299381),4,12,(328091566759774501/100000000000000000)⟩,⟨(200000000000000000/192481236479700619),0,4,(19159345201853549/500000000000000000)⟩,(160220289719504979/1000000000000000000)⟩
theorem valid412 : certificate412.Valid := by decide +kernel
theorem sound412 : 0 ≤ cappedLabelEntropy (certificate412.rho:ℝ) ∧ cappedLabelEntropy (certificate412.rho:ℝ) ≤ (certificate412.bound:ℝ) := rat_label_entropy_certificate_sound certificate412 valid412

def certificate413 : RatLabelEntropyCertificate := ⟨(9564625596881201/250000000000000000),⟨(250000000000000000/9564625596881201),4,12,(163169472938499563/50000000000000000)⟩,⟨(250000000000000000/240435374403118799),0,4,(39009577926917749/1000000000000000000)⟩,(8118476164821971/50000000000000000)⟩
theorem valid413 : certificate413.Valid := by decide +kernel
theorem sound413 : 0 ≤ cappedLabelEntropy (certificate413.rho:ℝ) ∧ cappedLabelEntropy (certificate413.rho:ℝ) ≤ (certificate413.bound:ℝ) := rat_label_entropy_certificate_sound certificate413 valid413

def certificate414 : RatLabelEntropyCertificate := ⟨(38950414304627399/1000000000000000000),⟨(1000000000000000000/38950414304627399),4,12,(3245465869889411357/1000000000000000000)⟩,⟨(1000000000000000000/961049585695372601),0,4,(19864636662449439/500000000000000000)⟩,(164594041912592819/1000000000000000000)⟩
theorem valid414 : certificate414.Valid := by decide +kernel
theorem sound414 : 0 ≤ cappedLabelEntropy (certificate414.rho:ℝ) ∧ cappedLabelEntropy (certificate414.rho:ℝ) ≤ (certificate414.bound:ℝ) := rat_label_entropy_certificate_sound certificate414 valid414

def certificate415 : RatLabelEntropyCertificate := ⟨(7925635105289079/200000000000000000),⟨(200000000000000000/7925635105289079),4,11,(3228214910527034533/1000000000000000000)⟩,⟨(200000000000000000/192074364894710921),0,4,(40434752348231497/1000000000000000000)⟩,(16676066399626097/100000000000000000)⟩
theorem valid415 : certificate415.Valid := by decide +kernel
theorem sound415 : 0 ≤ cappedLabelEntropy (certificate415.rho:ℝ) ∧ cappedLabelEntropy (certificate415.rho:ℝ) ≤ (certificate415.bound:ℝ) := rat_label_entropy_certificate_sound certificate415 valid415

def certificate416 : RatLabelEntropyCertificate := ⟨(23647316815651/1000000000000000000),⟨(1000000000000000000/23647316815651),15,8,(1331532612918298683/125000000000000000)⟩,⟨(1000000000000000000/999976352683184349),0,1,(369493694029/15625000000000000)⟩,(275544425600057/1000000000000000000)⟩
theorem valid416 : certificate416.Valid := by decide +kernel
theorem sound416 : 0 ≤ cappedLabelEntropy (certificate416.rho:ℝ) ∧ cappedLabelEntropy (certificate416.rho:ℝ) ≤ (certificate416.bound:ℝ) := rat_label_entropy_certificate_sound certificate416 valid416

def certificate417 : RatLabelEntropyCertificate := ⟨(18846285399509/1000000000000000000),⟨(1000000000000000000/18846285399509),15,12,(5439597362261668203/500000000000000000)⟩,⟨(1000000000000000000/999981153714600491),0,1,(9423231496489/500000000000000000)⟩,(111939258251179/500000000000000000)⟩
theorem valid417 : certificate417.Valid := by decide +kernel
theorem sound417 : 0 ≤ cappedLabelEntropy (certificate417.rho:ℝ) ∧ cappedLabelEntropy (certificate417.rho:ℝ) ≤ (certificate417.bound:ℝ) := rat_label_entropy_certificate_sound certificate417 valid417

def certificate418 : RatLabelEntropyCertificate := ⟨(5646709971359/31250000000000000),⟨(31250000000000000/5646709971359),12,9,(8618701585566314301/1000000000000000000)⟩,⟨(31250000000000000/31244353290028641),0,1,(180711046341103/1000000000000000000)⟩,(1738032254677667/1000000000000000000)⟩
theorem valid418 : certificate418.Valid := by decide +kernel
theorem sound418 : 0 ≤ cappedLabelEntropy (certificate418.rho:ℝ) ∧ cappedLabelEntropy (certificate418.rho:ℝ) ≤ (certificate418.bound:ℝ) := rat_label_entropy_certificate_sound certificate418 valid418

def certificate419 : RatLabelEntropyCertificate := ⟨(87069280380555283/1000000000000000000),⟨(1000000000000000000/87069280380555283),3,10,(2441051151013767441/1000000000000000000)⟩,⟨(1000000000000000000/912930719619444717),0,5,(91095283391834007/1000000000000000000)⟩,(18481515606983699/62500000000000000)⟩
theorem valid419 : certificate419.Valid := by decide +kernel
theorem sound419 : 0 ≤ cappedLabelEntropy (certificate419.rho:ℝ) ∧ cappedLabelEntropy (certificate419.rho:ℝ) ≤ (certificate419.bound:ℝ) := rat_label_entropy_certificate_sound certificate419 valid419

end Cycle12.CutLabelCertificates.Entropy020
