import Cycle12.RationalLabelEntropy
import Cycle12.RationalMinorityBudget

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CutLabelCertificates.Entropy026

def certificate520 : RatLabelEntropyCertificate := ⟨(6711400042742623/500000000000000000),⟨(500000000000000000/6711400042742623),6,6,(431080051901783411/100000000000000000)⟩,⟨(500000000000000000/493288599957257377),0,3,(13513700205752283/1000000000000000000)⟩,(17798830521164429/250000000000000000)⟩
theorem valid520 : certificate520.Valid := by decide +kernel
theorem sound520 : 0 ≤ cappedLabelEntropy (certificate520.rho:ℝ) ∧ cappedLabelEntropy (certificate520.rho:ℝ) ≤ (certificate520.bound:ℝ) := rat_label_entropy_certificate_sound certificate520 valid520

def certificate521 : RatLabelEntropyCertificate := ⟨(19092956978649437/200000000000000000),⟨(200000000000000000/19092956978649437),3,8,(1174498922035889123/500000000000000000)⟩,⟨(200000000000000000/180907043021350563),0,5,(100334041674424953/1000000000000000000)⟩,(315002247867519579/1000000000000000000)⟩
theorem valid521 : certificate521.Valid := by decide +kernel
theorem sound521 : 0 ≤ cappedLabelEntropy (certificate521.rho:ℝ) ∧ cappedLabelEntropy (certificate521.rho:ℝ) ≤ (certificate521.bound:ℝ) := rat_label_entropy_certificate_sound certificate521 valid521

def certificate522 : RatLabelEntropyCertificate := ⟨(1149789660376397/1000000000000000000),⟨(1000000000000000000/1149789660376397),9,13,(6768176257356482961/1000000000000000000)⟩,⟨(1000000000000000000/998850210339623603),0,2,(143806396953187/125000000000000000)⟩,(8931107479072499/1000000000000000000)⟩
theorem valid522 : certificate522.Valid := by decide +kernel
theorem sound522 : 0 ≤ cappedLabelEntropy (certificate522.rho:ℝ) ∧ cappedLabelEntropy (certificate522.rho:ℝ) ≤ (certificate522.bound:ℝ) := rat_label_entropy_certificate_sound certificate522 valid522

def certificate523 : RatLabelEntropyCertificate := ⟨(939158122765493/1000000000000000000),⟨(1000000000000000000/939158122765493),10,4,(108914479657521913/15625000000000000)⟩,⟨(1000000000000000000/999060841877234507),0,2,(117449926008503/125000000000000000)⟩,(58477685500849/7812500000000000)⟩
theorem valid523 : certificate523.Valid := by decide +kernel
theorem sound523 : 0 ≤ cappedLabelEntropy (certificate523.rho:ℝ) ∧ cappedLabelEntropy (certificate523.rho:ℝ) ≤ (certificate523.bound:ℝ) := rat_label_entropy_certificate_sound certificate523 valid523

def certificate524 : RatLabelEntropyCertificate := ⟨(1148502827499461/1000000000000000000),⟨(1000000000000000000/1148502827499461),9,13,(1353859214786357191/200000000000000000)⟩,⟨(1000000000000000000/998851497172500539),0,2,(1149162862288127/1000000000000000000)⟩,(8922398726583189/1000000000000000000)⟩
theorem valid524 : certificate524.Valid := by decide +kernel
theorem sound524 : 0 ≤ cappedLabelEntropy (certificate524.rho:ℝ) ∧ cappedLabelEntropy (certificate524.rho:ℝ) ≤ (certificate524.bound:ℝ) := rat_label_entropy_certificate_sound certificate524 valid524

def certificate525 : RatLabelEntropyCertificate := ⟨(13646089601429169/1000000000000000000),⟨(1000000000000000000/13646089601429169),6,6,(858860454895811183/200000000000000000)⟩,⟨(1000000000000000000/986353910398570831),0,3,(6870026642964181/500000000000000000)⟩,(72152988900822447/1000000000000000000)⟩
theorem valid525 : certificate525.Valid := by decide +kernel
theorem sound525 : 0 ≤ cappedLabelEntropy (certificate525.rho:ℝ) ∧ cappedLabelEntropy (certificate525.rho:ℝ) ≤ (certificate525.bound:ℝ) := rat_label_entropy_certificate_sound certificate525 valid525

def certificate526 : RatLabelEntropyCertificate := ⟨(9529988701386297/100000000000000000),⟨(100000000000000000/9529988701386297),3,9,(73460207934577899/31250000000000000)⟩,⟨(100000000000000000/90470011298613703),0,6,(100151757062489333/1000000000000000000)⟩,(31463129044795917/100000000000000000)⟩
theorem valid526 : certificate526.Valid := by decide +kernel
theorem sound526 : 0 ≤ cappedLabelEntropy (certificate526.rho:ℝ) ∧ cappedLabelEntropy (certificate526.rho:ℝ) ≤ (certificate526.bound:ℝ) := rat_label_entropy_certificate_sound certificate526 valid526

def certificate527 : RatLabelEntropyCertificate := ⟨(616335304844319/500000000000000000),⟨(500000000000000000/616335304844319),9,11,(6698572235916521107/1000000000000000000)⟩,⟨(500000000000000000/499383664695155681),0,2,(24668619460411/20000000000000000)⟩,(948904368100163/100000000000000000)⟩
theorem valid527 : certificate527.Valid := by decide +kernel
theorem sound527 : 0 ≤ cappedLabelEntropy (certificate527.rho:ℝ) ∧ cappedLabelEntropy (certificate527.rho:ℝ) ≤ (certificate527.bound:ℝ) := rat_label_entropy_certificate_sound certificate527 valid527

def certificate528 : RatLabelEntropyCertificate := ⟨(506567121943049/500000000000000000),⟨(500000000000000000/506567121943049),9,15,(6894706541384090951/1000000000000000000)⟩,⟨(500000000000000000/499493432878056951),0,2,(126705976411077/125000000000000000)⟩,(1599576829720293/200000000000000000)⟩
theorem valid528 : certificate528.Valid := by decide +kernel
theorem sound528 : 0 ≤ cappedLabelEntropy (certificate528.rho:ℝ) ∧ cappedLabelEntropy (certificate528.rho:ℝ) ≤ (certificate528.bound:ℝ) := rat_label_entropy_certificate_sound certificate528 valid528

def certificate529 : RatLabelEntropyCertificate := ⟨(1234179713101341/1000000000000000000),⟨(1000000000000000000/1234179713101341),9,12,(3348674364749313187/500000000000000000)⟩,⟨(1000000000000000000/998765820286898659),0,2,(246988388019613/200000000000000000)⟩,(1187393716665123/125000000000000000)⟩
theorem valid529 : certificate529.Valid := by decide +kernel
theorem sound529 : 0 ≤ cappedLabelEntropy (certificate529.rho:ℝ) ∧ cappedLabelEntropy (certificate529.rho:ℝ) ≤ (certificate529.bound:ℝ) := rat_label_entropy_certificate_sound certificate529 valid529

def certificate530 : RatLabelEntropyCertificate := ⟨(1713373786981847/125000000000000000),⟨(125000000000000000/1713373786981847),6,6,(857969867140635037/200000000000000000)⟩,⟨(125000000000000000/123286626213018153),0,3,(13801798440445709/1000000000000000000)⟩,(9051692567289957/125000000000000000)⟩
theorem valid530 : certificate530.Valid := by decide +kernel
theorem sound530 : 0 ≤ cappedLabelEntropy (certificate530.rho:ℝ) ∧ cappedLabelEntropy (certificate530.rho:ℝ) ≤ (certificate530.bound:ℝ) := rat_label_entropy_certificate_sound certificate530 valid530

def certificate531 : RatLabelEntropyCertificate := ⟨(95138337115914671/1000000000000000000),⟨(1000000000000000000/95138337115914671),3,8,(2352423266416278693/1000000000000000000)⟩,⟨(1000000000000000000/904861662884085329),0,6,(24993301414477461/250000000000000000)⟩,(314267558875102023/1000000000000000000)⟩
theorem valid531 : certificate531.Valid := by decide +kernel
theorem sound531 : 0 ≤ cappedLabelEntropy (certificate531.rho:ℝ) ∧ cappedLabelEntropy (certificate531.rho:ℝ) ≤ (certificate531.bound:ℝ) := rat_label_entropy_certificate_sound certificate531 valid531

def certificate532 : RatLabelEntropyCertificate := ⟨(1327923174289399/1000000000000000000),⟨(1000000000000000000/1327923174289399),9,11,(1656034770071750981/250000000000000000)⟩,⟨(1000000000000000000/998672076825710601),0,2,(1328805645590381/1000000000000000000)⟩,(5061694444104327/500000000000000000)⟩
theorem valid532 : certificate532.Valid := by decide +kernel
theorem sound532 : 0 ≤ cappedLabelEntropy (certificate532.rho:ℝ) ∧ cappedLabelEntropy (certificate532.rho:ℝ) ≤ (certificate532.bound:ℝ) := rat_label_entropy_certificate_sound certificate532 valid532

def certificate533 : RatLabelEntropyCertificate := ⟨(1090157909882509/1000000000000000000),⟨(1000000000000000000/1090157909882509),9,13,(6821432721782096983/1000000000000000000)⟩,⟨(1000000000000000000/998909842090117491),0,2,(1090752564234131/1000000000000000000)⟩,(1065750288760079/125000000000000000)⟩
theorem valid533 : certificate533.Valid := by decide +kernel
theorem sound533 : 0 ≤ cappedLabelEntropy (certificate533.rho:ℝ) ∧ cappedLabelEntropy (certificate533.rho:ℝ) ≤ (certificate533.bound:ℝ) := rat_label_entropy_certificate_sound certificate533 valid533

def certificate534 : RatLabelEntropyCertificate := ⟨(1316591256393417/1000000000000000000),⟨(1000000000000000000/1316591256393417),9,11,(51818041125020827/7812500000000000)⟩,⟨(1000000000000000000/998683408743606583),0,2,(52698348965821/40000000000000000)⟩,(5024145596347091/500000000000000000)⟩
theorem valid534 : certificate534.Valid := by decide +kernel
theorem sound534 : 0 ≤ cappedLabelEntropy (certificate534.rho:ℝ) ∧ cappedLabelEntropy (certificate534.rho:ℝ) ≤ (certificate534.bound:ℝ) := rat_label_entropy_certificate_sound certificate534 valid534

def certificate535 : RatLabelEntropyCertificate := ⟨(3401826081377699/250000000000000000),⟨(250000000000000000/3401826081377699),6,6,(2148574273829653693/500000000000000000)⟩,⟨(250000000000000000/246598173918622301),0,3,(428147881043523/31250000000000000)⟩,(71986910180881847/1000000000000000000)⟩
theorem valid535 : certificate535.Valid := by decide +kernel
theorem sound535 : 0 ≤ cappedLabelEntropy (certificate535.rho:ℝ) ∧ cappedLabelEntropy (certificate535.rho:ℝ) ≤ (certificate535.bound:ℝ) := rat_label_entropy_certificate_sound certificate535 valid535

def certificate536 : RatLabelEntropyCertificate := ⟨(94980270098310493/1000000000000000000),⟨(1000000000000000000/94980270098310493),3,9,(470817218425282477/200000000000000000)⟩,⟨(1000000000000000000/905019729901689507),0,6,(99798534523507201/1000000000000000000)⟩,(31391137562389181/100000000000000000)⟩
theorem valid536 : certificate536.Valid := by decide +kernel
theorem sound536 : 0 ≤ cappedLabelEntropy (certificate536.rho:ℝ) ∧ cappedLabelEntropy (certificate536.rho:ℝ) ≤ (certificate536.bound:ℝ) := rat_label_entropy_certificate_sound certificate536 valid536

def certificate537 : RatLabelEntropyCertificate := ⟨(361634789137533/250000000000000000),⟨(250000000000000000/361634789137533),9,9,(1307716272811219293/200000000000000000)⟩,⟨(250000000000000000/249638365210862467),0,2,(723793202180497/500000000000000000)⟩,(5451903192670357/500000000000000000)⟩
theorem valid537 : certificate537.Valid := by decide +kernel
theorem sound537 : 0 ≤ cappedLabelEntropy (certificate537.rho:ℝ) ∧ cappedLabelEntropy (certificate537.rho:ℝ) ≤ (certificate537.bound:ℝ) := rat_label_entropy_certificate_sound certificate537 valid537

def certificate538 : RatLabelEntropyCertificate := ⟨(585169699156243/500000000000000000),⟨(500000000000000000/585169699156243),9,12,(6750461488210943107/1000000000000000000)⟩,⟨(500000000000000000/499414830300843757),0,2,(11710247802713/10000000000000000)⟩,(9069985320278953/1000000000000000000)⟩
theorem valid538 : certificate538.Valid := by decide +kernel
theorem sound538 : 0 ≤ cappedLabelEntropy (certificate538.rho:ℝ) ∧ cappedLabelEntropy (certificate538.rho:ℝ) ≤ (certificate538.bound:ℝ) := rat_label_entropy_certificate_sound certificate538 valid538

def certificate539 : RatLabelEntropyCertificate := ⟨(351984054454177/250000000000000000),⟨(250000000000000000/351984054454177),9,9,(3282815161059221739/500000000000000000)⟩,⟨(250000000000000000/249648015945545823),0,2,(88058018206681/62500000000000000)⟩,(5325466666721697/500000000000000000)⟩
theorem valid539 : certificate539.Valid := by decide +kernel
theorem sound539 : 0 ≤ cappedLabelEntropy (certificate539.rho:ℝ) ∧ cappedLabelEntropy (certificate539.rho:ℝ) ≤ (certificate539.bound:ℝ) := rat_label_entropy_certificate_sound certificate539 valid539

end Cycle12.CutLabelCertificates.Entropy026
