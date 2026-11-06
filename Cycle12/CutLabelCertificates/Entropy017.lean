import Cycle12.RationalLabelEntropy
import Cycle12.RationalMinorityBudget

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CutLabelCertificates.Entropy017

def certificate340 : RatLabelEntropyCertificate := ⟨(937189209163793/1000000000000000000),⟨(1000000000000000000/937189209163793),10,4,(54473635666458263/7812500000000000)⟩,⟨(1000000000000000000/999062810790836207),0,2,(37505145821953/40000000000000000)⟩,(1867854790501791/250000000000000000)⟩
theorem valid340 : certificate340.Valid := by decide +kernel
theorem sound340 : 0 ≤ cappedLabelEntropy (certificate340.rho:ℝ) ∧ cappedLabelEntropy (certificate340.rho:ℝ) ≤ (certificate340.bound:ℝ) := rat_label_entropy_certificate_sound certificate340 valid340

def certificate341 : RatLabelEntropyCertificate := ⟨(559073975815131/500000000000000000),⟨(500000000000000000/559073975815131),9,14,(6796081577020729367/1000000000000000000)⟩,⟨(500000000000000000/499440926024184869),0,2,(279693386358057/250000000000000000)⟩,(1743309457108391/200000000000000000)⟩
theorem valid341 : certificate341.Valid := by decide +kernel
theorem sound341 : 0 ≤ cappedLabelEntropy (certificate341.rho:ℝ) ∧ cappedLabelEntropy (certificate341.rho:ℝ) ≤ (certificate341.bound:ℝ) := rat_label_entropy_certificate_sound certificate341 valid341

def certificate342 : RatLabelEntropyCertificate := ⟨(606669548824969/500000000000000000),⟨(500000000000000000/606669548824969),9,12,(3357189567601247027/500000000000000000)⟩,⟨(500000000000000000/499393330451175031),0,2,(242815157899571/200000000000000000)⟩,(9359421425061113/1000000000000000000)⟩
theorem valid342 : certificate342.Valid := by decide +kernel
theorem sound342 : 0 ≤ cappedLabelEntropy (certificate342.rho:ℝ) ∧ cappedLabelEntropy (certificate342.rho:ℝ) ≤ (certificate342.bound:ℝ) := rat_label_entropy_certificate_sound certificate342 valid342

def certificate343 : RatLabelEntropyCertificate := ⟨(263484643498311/200000000000000000),⟨(200000000000000000/263484643498311),9,11,(1658019389547707903/250000000000000000)⟩,⟨(200000000000000000/199736515356501689),0,2,(329572945596849/250000000000000000)⟩,(628362999346947/62500000000000000)⟩
theorem valid343 : certificate343.Valid := by decide +kernel
theorem sound343 : 0 ≤ cappedLabelEntropy (certificate343.rho:ℝ) ∧ cappedLabelEntropy (certificate343.rho:ℝ) ≤ (certificate343.bound:ℝ) := rat_label_entropy_certificate_sound certificate343 valid343

def certificate344 : RatLabelEntropyCertificate := ⟨(153336576215963/100000000000000000),⟨(100000000000000000/153336576215963),9,8,(6480290115144298031/1000000000000000000)⟩,⟨(100000000000000000/99846663423784037),0,2,(306908514115783/200000000000000000)⟩,(5734422273482183/500000000000000000)⟩
theorem valid344 : certificate344.Valid := by decide +kernel
theorem sound344 : 0 ≤ cappedLabelEntropy (certificate344.rho:ℝ) ∧ cappedLabelEntropy (certificate344.rho:ℝ) ≤ (certificate344.bound:ℝ) := rat_label_entropy_certificate_sound certificate344 valid344

def certificate345 : RatLabelEntropyCertificate := ⟨(1647331947207207/1000000000000000000),⟨(1000000000000000000/1647331947207207),9,7,(1281719660304103947/200000000000000000)⟩,⟨(1000000000000000000/998352668052792793),0,2,(1648690290445793/1000000000000000000)⟩,(12203063069171889/1000000000000000000)⟩
theorem valid345 : certificate345.Valid := by decide +kernel
theorem sound345 : 0 ≤ cappedLabelEntropy (certificate345.rho:ℝ) ∧ cappedLabelEntropy (certificate345.rho:ℝ) ≤ (certificate345.bound:ℝ) := rat_label_entropy_certificate_sound certificate345 valid345

def certificate346 : RatLabelEntropyCertificate := ⟨(70638291553483/40000000000000000),⟨(40000000000000000/70638291553483),9,5,(1267812472469861247/200000000000000000)⟩,⟨(40000000000000000/39929361708446517),0,2,(353503685923887/200000000000000000)⟩,(647945522537451/50000000000000000)⟩
theorem valid346 : certificate346.Valid := by decide +kernel
theorem sound346 : 0 ≤ cappedLabelEntropy (certificate346.rho:ℝ) ∧ cappedLabelEntropy (certificate346.rho:ℝ) ≤ (certificate346.bound:ℝ) := rat_label_entropy_certificate_sound certificate346 valid346

def certificate347 : RatLabelEntropyCertificate := ⟨(126026671876377/62500000000000000),⟨(62500000000000000/126026671876377),8,15,(1241285653923169423/200000000000000000)⟩,⟨(62500000000000000/62373973328123623),0,2,(504615618873919/250000000000000000)⟩,(7264600189356259/500000000000000000)⟩
theorem valid347 : certificate347.Valid := by decide +kernel
theorem sound347 : 0 ≤ cappedLabelEntropy (certificate347.rho:ℝ) ∧ cappedLabelEntropy (certificate347.rho:ℝ) ≤ (certificate347.bound:ℝ) := rat_label_entropy_certificate_sound certificate347 valid347

def certificate348 : RatLabelEntropyCertificate := ⟨(107387372813781/50000000000000000),⟨(50000000000000000/107387372813781),8,14,(1228667136162776419/200000000000000000)⟩,⟨(50000000000000000/49892612627186219),0,2,(107502858678123/50000000000000000)⟩,(3834943243813091/250000000000000000)⟩
theorem valid348 : certificate348.Valid := by decide +kernel
theorem sound348 : 0 ≤ cappedLabelEntropy (certificate348.rho:ℝ) ∧ cappedLabelEntropy (certificate348.rho:ℝ) ≤ (certificate348.bound:ℝ) := rat_label_entropy_certificate_sound certificate348 valid348

def certificate349 : RatLabelEntropyCertificate := ⟨(456789981949581/200000000000000000),⟨(200000000000000000/456789981949581),8,13,(1520462229590587847/250000000000000000)⟩,⟨(200000000000000000/199543210018050419),0,2,(2286562101511059/1000000000000000000)⟩,(8085988998199883/500000000000000000)⟩
theorem valid349 : certificate349.Valid := by decide +kernel
theorem sound349 : 0 ≤ cappedLabelEntropy (certificate349.rho:ℝ) ∧ cappedLabelEntropy (certificate349.rho:ℝ) ≤ (certificate349.bound:ℝ) := rat_label_entropy_certificate_sound certificate349 valid349

def certificate350 : RatLabelEntropyCertificate := ⟨(321235481292493/125000000000000000),⟨(125000000000000000/321235481292493),8,11,(2981947287758281229/500000000000000000)⟩,⟨(125000000000000000/124678764518707507),0,2,(2573191670199279/1000000000000000000)⟩,(3578619044246443/200000000000000000)⟩
theorem valid350 : certificate350.Valid := by decide +kernel
theorem sound350 : 0 ≤ cappedLabelEntropy (certificate350.rho:ℝ) ∧ cappedLabelEntropy (certificate350.rho:ℝ) ≤ (certificate350.bound:ℝ) := rat_label_entropy_certificate_sound certificate350 valid350

def certificate351 : RatLabelEntropyCertificate := ⟨(285162471686277/100000000000000000),⟨(100000000000000000/285162471686277),8,9,(585986637104102401/100000000000000000)⟩,⟨(100000000000000000/99714837528313723),0,2,(2855698344774167/1000000000000000000)⟩,(19557694745963833/1000000000000000000)⟩
theorem valid351 : certificate351.Valid := by decide +kernel
theorem sound351 : 0 ≤ cappedLabelEntropy (certificate351.rho:ℝ) ∧ cappedLabelEntropy (certificate351.rho:ℝ) ≤ (certificate351.bound:ℝ) := rat_label_entropy_certificate_sound certificate351 valid351

def certificate352 : RatLabelEntropyCertificate := ⟨(1504235989406641/500000000000000000),⟨(500000000000000000/1504235989406641),8,8,(29031614886765663/5000000000000000)⟩,⟨(500000000000000000/498495764010593359),0,2,(1506503263814699/500000000000000000)⟩,(409442039184513/20000000000000000)⟩
theorem valid352 : certificate352.Valid := by decide +kernel
theorem sound352 : 0 ≤ cappedLabelEntropy (certificate352.rho:ℝ) ∧ cappedLabelEntropy (certificate352.rho:ℝ) ≤ (certificate352.bound:ℝ) := rat_label_entropy_certificate_sound certificate352 valid352

def certificate353 : RatLabelEntropyCertificate := ⟨(1585277991221893/500000000000000000),⟨(500000000000000000/1585277991221893),8,7,(5753848317688233639/1000000000000000000)⟩,⟨(500000000000000000/498414722008778107),0,2,(3175592844315411/1000000000000000000)⟩,(5352105663786401/250000000000000000)⟩
theorem valid353 : certificate353.Valid := by decide +kernel
theorem sound353 : 0 ≤ cappedLabelEntropy (certificate353.rho:ℝ) ∧ cappedLabelEntropy (certificate353.rho:ℝ) ≤ (certificate353.bound:ℝ) := rat_label_entropy_certificate_sound certificate353 valid353

def certificate354 : RatLabelEntropyCertificate := ⟨(1752115035114009/500000000000000000),⟨(500000000000000000/1752115035114009),8,6,(2826892224375910663/500000000000000000)⟩,⟨(500000000000000000/498247884964885991),0,2,(3510384265771551/1000000000000000000)⟩,(466204890951461/20000000000000000)⟩
theorem valid354 : certificate354.Valid := by decide +kernel
theorem sound354 : 0 ≤ cappedLabelEntropy (certificate354.rho:ℝ) ∧ cappedLabelEntropy (certificate354.rho:ℝ) ≤ (certificate354.bound:ℝ) := rat_label_entropy_certificate_sound certificate354 valid354

def certificate355 : RatLabelEntropyCertificate := ⟨(3860434472410023/1000000000000000000),⟨(1000000000000000000/3860434472410023),8,3,(1111395108844070827/200000000000000000)⟩,⟨(1000000000000000000/996139565527589977),0,2,(1933952591278657/500000000000000000)⟩,(1265265667065113/50000000000000000)⟩
theorem valid355 : certificate355.Valid := by decide +kernel
theorem sound355 : 0 ≤ cappedLabelEntropy (certificate355.rho:ℝ) ∧ cappedLabelEntropy (certificate355.rho:ℝ) ≤ (certificate355.bound:ℝ) := rat_label_entropy_certificate_sound certificate355 valid355

def certificate356 : RatLabelEntropyCertificate := ⟨(2022268514249651/500000000000000000),⟨(500000000000000000/2022268514249651),7,15,(86099815473058691/15625000000000000)⟩,⟨(500000000000000000/497977731485750349),0,2,(4052738289391697/1000000000000000000)⟩,(26323315916288989/1000000000000000000)⟩
theorem valid356 : certificate356.Valid := by decide +kernel
theorem sound356 : 0 ≤ cappedLabelEntropy (certificate356.rho:ℝ) ∧ cappedLabelEntropy (certificate356.rho:ℝ) ≤ (certificate356.bound:ℝ) := rat_label_entropy_certificate_sound certificate356 valid356

def certificate357 : RatLabelEntropyCertificate := ⟨(4234346635925299/1000000000000000000),⟨(1000000000000000000/4234346635925299),7,14,(5464526240011409897/1000000000000000000)⟩,⟨(1000000000000000000/995765653364074701),0,2,(2121668434563211/500000000000000000)⟩,(1710254213202961/62500000000000000)⟩
theorem valid357 : certificate357.Valid := by decide +kernel
theorem sound357 : 0 ≤ cappedLabelEntropy (certificate357.rho:ℝ) ∧ cappedLabelEntropy (certificate357.rho:ℝ) ≤ (certificate357.bound:ℝ) := rat_label_entropy_certificate_sound certificate357 valid357

def certificate358 : RatLabelEntropyCertificate := ⟨(177157040043639/40000000000000000),⟨(40000000000000000/177157040043639),7,13,(541959816199483791/100000000000000000)⟩,⟨(40000000000000000/39822842959956361),0,2,(2219381374374559/500000000000000000)⟩,(5684420602424461/200000000000000000)⟩
theorem valid358 : certificate358.Valid := by decide +kernel
theorem sound358 : 0 ≤ cappedLabelEntropy (certificate358.rho:ℝ) ∧ cappedLabelEntropy (certificate358.rho:ℝ) ≤ (certificate358.bound:ℝ) := rat_label_entropy_certificate_sound certificate358 valid358

def certificate359 : RatLabelEntropyCertificate := ⟨(1158565214802241/250000000000000000),⟨(250000000000000000/1158565214802241),7,12,(1074855712421449747/200000000000000000)⟩,⟨(250000000000000000/248841434785197759),0,2,(4645032337508403/1000000000000000000)⟩,(29529314832816383/1000000000000000000)⟩
theorem valid359 : certificate359.Valid := by decide +kernel
theorem sound359 : 0 ≤ cappedLabelEntropy (certificate359.rho:ℝ) ∧ cappedLabelEntropy (certificate359.rho:ℝ) ≤ (certificate359.bound:ℝ) := rat_label_entropy_certificate_sound certificate359 valid359

end Cycle12.CutLabelCertificates.Entropy017
