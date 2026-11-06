import Cycle12.RationalLabelEntropy
import Cycle12.RationalMinorityBudget

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CutLabelCertificates.Entropy024

def certificate480 : RatLabelEntropyCertificate := ⟨(3432876151115499/250000000000000000),⟨(250000000000000000/3432876151115499),6,6,(4288062480030600689/1000000000000000000)⟩,⟨(250000000000000000/246567123848884501),0,3,(6913326872564799/500000000000000000)⟩,(72518342674324969/1000000000000000000)⟩
theorem valid480 : certificate480.Valid := by decide +kernel
theorem sound480 : 0 ≤ cappedLabelEntropy (certificate480.rho:ℝ) ∧ cappedLabelEntropy (certificate480.rho:ℝ) ≤ (certificate480.bound:ℝ) := rat_label_entropy_certificate_sound certificate480 valid480

def certificate481 : RatLabelEntropyCertificate := ⟨(91741053971003023/1000000000000000000),⟨(1000000000000000000/91741053971003023),3,9,(2388785301204557549/1000000000000000000)⟩,⟨(1000000000000000000/908258946028996977),0,5,(48112879093212631/500000000000000000)⟩,(306547586954189763/1000000000000000000)⟩
theorem valid481 : certificate481.Valid := by decide +kernel
theorem sound481 : 0 ≤ cappedLabelEntropy (certificate481.rho:ℝ) ∧ cappedLabelEntropy (certificate481.rho:ℝ) ≤ (certificate481.bound:ℝ) := rat_label_entropy_certificate_sound certificate481 valid481

def certificate482 : RatLabelEntropyCertificate := ⟨(560670459951393/1000000000000000000),⟨(1000000000000000000/560670459951393),10,14,(7486377240454018961/1000000000000000000)⟩,⟨(1000000000000000000/999439329540048607),0,1,(112165538881523/200000000000000000)⟩,(2378951912830617/500000000000000000)⟩
theorem valid482 : certificate482.Valid := by decide +kernel
theorem sound482 : 0 ≤ cappedLabelEntropy (certificate482.rho:ℝ) ∧ cappedLabelEntropy (certificate482.rho:ℝ) ≤ (certificate482.bound:ℝ) := rat_label_entropy_certificate_sound certificate482 valid482

def certificate483 : RatLabelEntropyCertificate := ⟨(3514560845081/7812500000000000),⟨(7812500000000000/3514560845081),11,5,(963320714246925689/125000000000000000)⟩,⟨(7812500000000000/7808985439154919),0,1,(44996500724199/100000000000000000)⟩,(3916667430152141/1000000000000000000)⟩
theorem valid483 : certificate483.Valid := by decide +kernel
theorem sound483 : 0 ≤ cappedLabelEntropy (certificate483.rho:ℝ) ∧ cappedLabelEntropy (certificate483.rho:ℝ) ≤ (certificate483.bound:ℝ) := rat_label_entropy_certificate_sound certificate483 valid483

def certificate484 : RatLabelEntropyCertificate := ⟨(686868222778787/1000000000000000000),⟨(1000000000000000000/686868222778787),10,10,(56901313278133937/7812500000000000)⟩,⟨(1000000000000000000/999313131777221213),0,2,(343552112415457/500000000000000000)⟩,(568934637718989/100000000000000000)⟩
theorem valid484 : certificate484.Valid := by decide +kernel
theorem sound484 : 0 ≤ cappedLabelEntropy (certificate484.rho:ℝ) ∧ cappedLabelEntropy (certificate484.rho:ℝ) ≤ (certificate484.bound:ℝ) := rat_label_entropy_certificate_sound certificate484 valid484

def certificate485 : RatLabelEntropyCertificate := ⟨(3835968341416519/250000000000000000),⟨(250000000000000000/3835968341416519),6,3,(522129876736848501/125000000000000000)⟩,⟨(250000000000000000/246164031658583481),0,3,(3092561755808211/200000000000000000)⟩,(19829376767976567/250000000000000000)⟩
theorem valid485 : certificate485.Valid := by decide +kernel
theorem sound485 : 0 ≤ cappedLabelEntropy (certificate485.rho:ℝ) ∧ cappedLabelEntropy (certificate485.rho:ℝ) ≤ (certificate485.bound:ℝ) := rat_label_entropy_certificate_sound certificate485 valid485

def certificate486 : RatLabelEntropyCertificate := ⟨(91606749611177899/1000000000000000000),⟨(1000000000000000000/91606749611177899),3,9,(2390250324305162043/1000000000000000000)⟩,⟨(1000000000000000000/908393250388822101),0,5,(48038949498800097/500000000000000000)⟩,(306239577927618743/1000000000000000000)⟩
theorem valid486 : certificate486.Valid := by decide +kernel
theorem sound486 : 0 ≤ cappedLabelEntropy (certificate486.rho:ℝ) ∧ cappedLabelEntropy (certificate486.rho:ℝ) ≤ (certificate486.bound:ℝ) := rat_label_entropy_certificate_sound certificate486 valid486

def certificate487 : RatLabelEntropyCertificate := ⟨(620149356491779/1000000000000000000),⟨(1000000000000000000/620149356491779),10,11,(1846387552842227829/250000000000000000)⟩,⟨(1000000000000000000/999379850643508221),0,2,(310170864320523/500000000000000000)⟩,(5200101235035377/1000000000000000000)⟩
theorem valid487 : certificate487.Valid := by decide +kernel
theorem sound487 : 0 ≤ cappedLabelEntropy (certificate487.rho:ℝ) ∧ cappedLabelEntropy (certificate487.rho:ℝ) ≤ (certificate487.bound:ℝ) := rat_label_entropy_certificate_sound certificate487 valid487

def certificate488 : RatLabelEntropyCertificate := ⟨(499934211858999/1000000000000000000),⟨(1000000000000000000/499934211858999),10,16,(3800517022240501363/500000000000000000)⟩,⟨(1000000000000000000/999500065788141001),0,1,(250029610316469/500000000000000000)⟩,(2149913094130809/500000000000000000)⟩
theorem valid488 : certificate488.Valid := by decide +kernel
theorem sound488 : 0 ≤ cappedLabelEntropy (certificate488.rho:ℝ) ∧ cappedLabelEntropy (certificate488.rho:ℝ) ≤ (certificate488.bound:ℝ) := rat_label_entropy_certificate_sound certificate488 valid488

def certificate489 : RatLabelEntropyCertificate := ⟨(185736170852383/250000000000000000),⟨(250000000000000000/185736170852383),10,9,(1801222241585430633/250000000000000000)⟩,⟨(250000000000000000/249814263829147617),0,2,(92902600447581/125000000000000000)⟩,(609550258373561/100000000000000000)⟩
theorem valid489 : certificate489.Valid := by decide +kernel
theorem sound489 : 0 ≤ cappedLabelEntropy (certificate489.rho:ℝ) ∧ cappedLabelEntropy (certificate489.rho:ℝ) ≤ (certificate489.bound:ℝ) := rat_label_entropy_certificate_sound certificate489 valid489

def certificate490 : RatLabelEntropyCertificate := ⟨(17051237164279213/1000000000000000000),⟨(1000000000000000000/17051237164279213),5,14,(814306503386047489/200000000000000000)⟩,⟨(1000000000000000000/982948762835720787),0,3,(8599141726564409/500000000000000000)⟩,(86329698011403169/1000000000000000000)⟩
theorem valid490 : certificate490.Valid := by decide +kernel
theorem sound490 : 0 ≤ cappedLabelEntropy (certificate490.rho:ℝ) ∧ cappedLabelEntropy (certificate490.rho:ℝ) ≤ (certificate490.bound:ℝ) := rat_label_entropy_certificate_sound certificate490 valid490

def certificate491 : RatLabelEntropyCertificate := ⟨(45737364793704053/500000000000000000),⟨(500000000000000000/45737364793704053),3,9,(2391692524217796669/1000000000000000000)⟩,⟨(500000000000000000/454262635206295947),0,5,(47966287999403909/500000000000000000)⟩,(305936596459741859/1000000000000000000)⟩
theorem valid491 : certificate491.Valid := by decide +kernel
theorem sound491 : 0 ≤ cappedLabelEntropy (certificate491.rho:ℝ) ∧ cappedLabelEntropy (certificate491.rho:ℝ) ≤ (certificate491.bound:ℝ) := rat_label_entropy_certificate_sound certificate491 valid491

def certificate492 : RatLabelEntropyCertificate := ⟨(686557940551871/1000000000000000000),⟨(1000000000000000000/686557940551871),10,10,(145676398727756597/20000000000000000)⟩,⟨(1000000000000000000/999313442059448129),0,2,(85849216172839/125000000000000000)⟩,(1421771655142843/250000000000000000)⟩
theorem valid492 : certificate492.Valid := by decide +kernel
theorem sound492 : 0 ≤ cappedLabelEntropy (certificate492.rho:ℝ) ∧ cappedLabelEntropy (certificate492.rho:ℝ) ≤ (certificate492.bound:ℝ) := rat_label_entropy_certificate_sound certificate492 valid492

def certificate493 : RatLabelEntropyCertificate := ⟨(280327903939017/500000000000000000),⟨(500000000000000000/280327903939017),10,13,(7486403373924321403/1000000000000000000)⟩,⟨(500000000000000000/499719672096060983),0,1,(56081303411477/100000000000000000)⟩,(118944853568461/25000000000000000)⟩
theorem valid493 : certificate493.Valid := by decide +kernel
theorem sound493 : 0 ≤ cappedLabelEntropy (certificate493.rho:ℝ) ∧ cappedLabelEntropy (certificate493.rho:ℝ) ≤ (certificate493.bound:ℝ) := rat_label_entropy_certificate_sound certificate493 valid493

def certificate494 : RatLabelEntropyCertificate := ⟨(157593048151257/200000000000000000),⟨(200000000000000000/157593048151257),10,8,(178651414494866889/25000000000000000)⟩,⟨(200000000000000000/199842406951848743),0,2,(3153103394171/4000000000000000)⟩,(6418498907929917/1000000000000000000)⟩
theorem valid494 : certificate494.Valid := by decide +kernel
theorem sound494 : 0 ≤ cappedLabelEntropy (certificate494.rho:ℝ) ∧ cappedLabelEntropy (certificate494.rho:ℝ) ≤ (certificate494.bound:ℝ) := rat_label_entropy_certificate_sound certificate494 valid494

def certificate495 : RatLabelEntropyCertificate := ⟨(19031510577434577/1000000000000000000),⟨(1000000000000000000/19031510577434577),5,12,(1980829611041877029/500000000000000000)⟩,⟨(1000000000000000000/980968489422565423),0,3,(9607470403350827/500000000000000000)⟩,(5890350677923271/62500000000000000)⟩
theorem valid495 : certificate495.Valid := by decide +kernel
theorem sound495 : 0 ≤ cappedLabelEntropy (certificate495.rho:ℝ) ∧ cappedLabelEntropy (certificate495.rho:ℝ) ≤ (certificate495.bound:ℝ) := rat_label_entropy_certificate_sound certificate495 valid495

def certificate496 : RatLabelEntropyCertificate := ⟨(2304410376386127/25000000000000000),⟨(25000000000000000/2304410376386127),3,9,(2384050983144181711/1000000000000000000)⟩,⟨(25000000000000000/22695589623613873),0,5,(96705208966174227/1000000000000000000)⟩,(307544542422124599/1000000000000000000)⟩
theorem valid496 : certificate496.Valid := by decide +kernel
theorem sound496 : 0 ≤ cappedLabelEntropy (certificate496.rho:ℝ) ∧ cappedLabelEntropy (certificate496.rho:ℝ) ≤ (certificate496.bound:ℝ) := rat_label_entropy_certificate_sound certificate496 valid496

def certificate497 : RatLabelEntropyCertificate := ⟨(94456147819733/125000000000000000),⟨(125000000000000000/94456147819733),10,8,(7187933333722217283/1000000000000000000)⟩,⟨(125000000000000000/124905543852180267),0,2,(188983707327409/250000000000000000)⟩,(6186919555681417/1000000000000000000)⟩
theorem valid497 : certificate497.Valid := by decide +kernel
theorem sound497 : 0 ≤ cappedLabelEntropy (certificate497.rho:ℝ) ∧ cappedLabelEntropy (certificate497.rho:ℝ) ≤ (certificate497.bound:ℝ) := rat_label_entropy_certificate_sound certificate497 valid497

def certificate498 : RatLabelEntropyCertificate := ⟨(38166818363611/62500000000000000),⟨(62500000000000000/38166818363611),10,12,(7400955326813778943/1000000000000000000)⟩,⟨(62500000000000000/62461833181636389),0,1,(610855628133209/1000000000000000000)⟩,(5130017280291537/1000000000000000000)⟩
theorem valid498 : certificate498.Valid := by decide +kernel
theorem sound498 : 0 ≤ cappedLabelEntropy (certificate498.rho:ℝ) ∧ cappedLabelEntropy (certificate498.rho:ℝ) ≤ (certificate498.bound:ℝ) := rat_label_entropy_certificate_sound certificate498 valid498

def certificate499 : RatLabelEntropyCertificate := ⟨(169060223419187/200000000000000000),⟨(200000000000000000/169060223419187),10,6,(3537908821246213357/500000000000000000)⟩,⟨(200000000000000000/199830939776580813),0,2,(845658585545067/1000000000000000000)⟩,(3413070153481999/500000000000000000)⟩
theorem valid499 : certificate499.Valid := by decide +kernel
theorem sound499 : 0 ≤ cappedLabelEntropy (certificate499.rho:ℝ) ∧ cappedLabelEntropy (certificate499.rho:ℝ) ≤ (certificate499.bound:ℝ) := rat_label_entropy_certificate_sound certificate499 valid499

end Cycle12.CutLabelCertificates.Entropy024
