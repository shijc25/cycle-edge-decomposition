import Cycle12.RationalLabelEntropy
import Cycle12.RationalMinorityBudget

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CutLabelCertificates.Entropy021

def certificate420 : RatLabelEntropyCertificate := ⟨(9430189596691/250000000000000000),⟨(250000000000000000/9430189596691),14,12,(10185299994707496781/1000000000000000000)⟩,⟨(250000000000000000/249990569810403309),0,1,(18860734916231/500000000000000000)⟩,(421917287147083/1000000000000000000)⟩
theorem valid420 : certificate420.Valid := by decide +kernel
theorem sound420 : 0 ≤ cappedLabelEntropy (certificate420.rho:ℝ) ∧ cappedLabelEntropy (certificate420.rho:ℝ) ≤ (certificate420.bound:ℝ) := rat_label_entropy_certificate_sound certificate420 valid420

def certificate421 : RatLabelEntropyCertificate := ⟨(14773449974357/500000000000000000),⟨(500000000000000000/14773449974357),15,4,(10429531728288427713/1000000000000000000)⟩,⟨(500000000000000000/499985226550025643),0,1,(29547336466961/1000000000000000000)⟩,(84426698480611/250000000000000000)⟩
theorem valid421 : certificate421.Valid := by decide +kernel
theorem sound421 : 0 ≤ cappedLabelEntropy (certificate421.rho:ℝ) ∧ cappedLabelEntropy (certificate421.rho:ℝ) ≤ (certificate421.bound:ℝ) := rat_label_entropy_certificate_sound certificate421 valid421

def certificate422 : RatLabelEntropyCertificate := ⟨(39655131659369/200000000000000000),⟨(200000000000000000/39655131659369),12,7,(8525852281880140113/1000000000000000000)⟩,⟨(200000000000000000/199960344868340631),0,1,(99147658756927/500000000000000000)⟩,(47218124352767/25000000000000000)⟩
theorem valid422 : certificate422.Valid := by decide +kernel
theorem sound422 : 0 ≤ cappedLabelEntropy (certificate422.rho:ℝ) ∧ cappedLabelEntropy (certificate422.rho:ℝ) ≤ (certificate422.bound:ℝ) := rat_label_entropy_certificate_sound certificate422 valid422

def certificate423 : RatLabelEntropyCertificate := ⟨(86605773895689307/1000000000000000000),⟨(1000000000000000000/86605773895689307),3,10,(1223194396237959671/500000000000000000)⟩,⟨(1000000000000000000/913394226104310693),0,5,(18117539914681831/200000000000000000)⟩,(18413354773033857/62500000000000000)⟩
theorem valid423 : certificate423.Valid := by decide +kernel
theorem sound423 : 0 ≤ cappedLabelEntropy (certificate423.rho:ℝ) ∧ cappedLabelEntropy (certificate423.rho:ℝ) ≤ (certificate423.bound:ℝ) := rat_label_entropy_certificate_sound certificate423 valid423

def certificate424 : RatLabelEntropyCertificate := ⟨(54034530924789/1000000000000000000),⟨(1000000000000000000/54034530924789),14,6,(9825887254198263717/1000000000000000000)⟩,⟨(1000000000000000000/999945965469075211),0,1,(54035990842647/1000000000000000000)⟩,(116994055946739/200000000000000000)⟩
theorem valid424 : certificate424.Valid := by decide +kernel
theorem sound424 : 0 ≤ cappedLabelEntropy (certificate424.rho:ℝ) ∧ cappedLabelEntropy (certificate424.rho:ℝ) ≤ (certificate424.bound:ℝ) := rat_label_entropy_certificate_sound certificate424 valid424

def certificate425 : RatLabelEntropyCertificate := ⟨(42631583816299/1000000000000000000),⟨(1000000000000000000/42631583816299),14,10,(10062915175254753921/1000000000000000000)⟩,⟨(1000000000000000000/999957368416183701),0,1,(42632492568097/1000000000000000000)⟩,(471628686807597/1000000000000000000)⟩
theorem valid425 : certificate425.Valid := by decide +kernel
theorem sound425 : 0 ≤ cappedLabelEntropy (certificate425.rho:ℝ) ∧ cappedLabelEntropy (certificate425.rho:ℝ) ≤ (certificate425.bound:ℝ) := rat_label_entropy_certificate_sound certificate425 valid425

def certificate426 : RatLabelEntropyCertificate := ⟨(21523704343089/100000000000000000),⟨(100000000000000000/21523704343089),12,6,(8443770609588251853/1000000000000000000)⟩,⟨(100000000000000000/99978476295656911),0,1,(215260210247621/1000000000000000000)⟩,(2032626099692819/1000000000000000000)⟩
theorem valid426 : certificate426.Valid := by decide +kernel
theorem sound426 : 0 ≤ cappedLabelEntropy (certificate426.rho:ℝ) ∧ cappedLabelEntropy (certificate426.rho:ℝ) ≤ (certificate426.bound:ℝ) := rat_label_entropy_certificate_sound certificate426 valid426

def certificate427 : RatLabelEntropyCertificate := ⟨(42408584175019/488281250000000),⟨(488281250000000/42408584175019),3,10,(2443540773100612523/1000000000000000000)⟩,⟨(488281250000000/445872665824981),0,5,(90858163183019491/1000000000000000000)⟩,(36899398653824607/125000000000000000)⟩
theorem valid427 : certificate427.Valid := by decide +kernel
theorem sound427 : 0 ≤ cappedLabelEntropy (certificate427.rho:ℝ) ∧ cappedLabelEntropy (certificate427.rho:ℝ) ≤ (certificate427.bound:ℝ) := rat_label_entropy_certificate_sound certificate427 valid427

def certificate428 : RatLabelEntropyCertificate := ⟨(18583953996691/250000000000000000),⟨(250000000000000000/18583953996691),13,12,(2376729419201230121/250000000000000000)⟩,⟨(250000000000000000/249981416046003309),0,1,(74338579030463/1000000000000000000)⟩,(97629692004477/125000000000000000)⟩
theorem valid428 : certificate428.Valid := by decide +kernel
theorem sound428 : 0 ≤ cappedLabelEntropy (certificate428.rho:ℝ) ∧ cappedLabelEntropy (certificate428.rho:ℝ) ≤ (certificate428.bound:ℝ) := rat_label_entropy_certificate_sound certificate428 valid428

def certificate429 : RatLabelEntropyCertificate := ⟨(58621997342529/1000000000000000000),⟨(1000000000000000000/58621997342529),14,4,(487220027527370201/50000000000000000)⟩,⟨(1000000000000000000/999941378002657471),0,1,(58623715678971/1000000000000000000)⟩,(125971300443679/200000000000000000)⟩
theorem valid429 : certificate429.Valid := by decide +kernel
theorem sound429 : 0 ≤ cappedLabelEntropy (certificate429.rho:ℝ) ∧ cappedLabelEntropy (certificate429.rho:ℝ) ≤ (certificate429.bound:ℝ) := rat_label_entropy_certificate_sound certificate429 valid429

def certificate430 : RatLabelEntropyCertificate := ⟨(9666438356829/40000000000000000),⟨(40000000000000000/9666438356829),12,3,(4163987405157846729/500000000000000000)⟩,⟨(40000000000000000/39990333561643171),0,1,(120845081817723/500000000000000000)⟩,(1127089067543637/500000000000000000)⟩
theorem valid430 : certificate430.Valid := by decide +kernel
theorem sound430 : 0 ≤ cappedLabelEntropy (certificate430.rho:ℝ) ∧ cappedLabelEntropy (certificate430.rho:ℝ) ≤ (certificate430.bound:ℝ) := rat_label_entropy_certificate_sound certificate430 valid430

def certificate431 : RatLabelEntropyCertificate := ⟨(11219411914095627/125000000000000000),⟨(125000000000000000/11219411914095627),3,10,(482133650530977989/200000000000000000)⟩,⟨(125000000000000000/113780588085904373),0,5,(94041809370337839/1000000000000000000)⟩,(301971299916703289/1000000000000000000)⟩
theorem valid431 : certificate431.Valid := by decide +kernel
theorem sound431 : 0 ≤ cappedLabelEntropy (certificate431.rho:ℝ) ∧ cappedLabelEntropy (certificate431.rho:ℝ) ≤ (certificate431.bound:ℝ) := rat_label_entropy_certificate_sound certificate431 valid431

def certificate432 : RatLabelEntropyCertificate := ⟨(97285638889851/1000000000000000000),⟨(1000000000000000000/97285638889851),13,8,(9237859175864564779/1000000000000000000)⟩,⟨(1000000000000000000/999902714361110149),0,1,(97290371444561/1000000000000000000)⟩,(497995969193537/500000000000000000)⟩
theorem valid432 : certificate432.Valid := by decide +kernel
theorem sound432 : 0 ≤ cappedLabelEntropy (certificate432.rho:ℝ) ∧ cappedLabelEntropy (certificate432.rho:ℝ) ≤ (certificate432.bound:ℝ) := rat_label_entropy_certificate_sound certificate432 valid432

def certificate433 : RatLabelEntropyCertificate := ⟨(38386580016597/500000000000000000),⟨(500000000000000000/38386580016597),13,12,(9474655457627025301/1000000000000000000)⟩,⟨(500000000000000000/499961613419983403),0,1,(76776107243091/1000000000000000000)⟩,(402084726303249/500000000000000000)⟩
theorem valid433 : certificate433.Valid := by decide +kernel
theorem sound433 : 0 ≤ cappedLabelEntropy (certificate433.rho:ℝ) ∧ cappedLabelEntropy (certificate433.rho:ℝ) ≤ (certificate433.bound:ℝ) := rat_label_entropy_certificate_sound certificate433 valid433

def certificate434 : RatLabelEntropyCertificate := ⟨(33381395398129/125000000000000000),⟨(125000000000000000/33381395398129),11,14,(8228070295505404449/1000000000000000000)⟩,⟨(125000000000000000/124966618604601871),0,1,(267086827696553/1000000000000000000)⟩,(1232165622515737/500000000000000000)⟩
theorem valid434 : certificate434.Valid := by decide +kernel
theorem sound434 : 0 ≤ cappedLabelEntropy (certificate434.rho:ℝ) ∧ cappedLabelEntropy (certificate434.rho:ℝ) ≤ (certificate434.bound:ℝ) := rat_label_entropy_certificate_sound certificate434 valid434

def certificate435 : RatLabelEntropyCertificate := ⟨(5601801460169217/62500000000000000),⟨(62500000000000000/5601801460169217),3,9,(60301958035405869/25000000000000000)⟩,⟨(62500000000000000/56898198539830783),0,5,(93902876219684481/1000000000000000000)⟩,(150839106860485921/500000000000000000)⟩
theorem valid435 : certificate435.Valid := by decide +kernel
theorem sound435 : 0 ≤ cappedLabelEntropy (certificate435.rho:ℝ) ∧ cappedLabelEntropy (certificate435.rho:ℝ) ≤ (certificate435.bound:ℝ) := rat_label_entropy_certificate_sound certificate435 valid435

def certificate436 : RatLabelEntropyCertificate := ⟨(122399458993017/1000000000000000000),⟨(1000000000000000000/122399458993017),12,16,(4504110303943753883/500000000000000000)⟩,⟨(1000000000000000000/999877600541006983),0,1,(61203475209051/500000000000000000)⟩,(306248324192193/250000000000000000)⟩
theorem valid436 : certificate436.Valid := by decide +kernel
theorem sound436 : 0 ≤ cappedLabelEntropy (certificate436.rho:ℝ) ∧ cappedLabelEntropy (certificate436.rho:ℝ) ≤ (certificate436.bound:ℝ) := rat_label_entropy_certificate_sound certificate436 valid436

def certificate437 : RatLabelEntropyCertificate := ⟨(97429610729101/1000000000000000000),⟨(1000000000000000000/97429610729101),13,8,(230909509548138309/25000000000000000)⟩,⟨(1000000000000000000/999902570389270899),0,1,(24358589325483/250000000000000000)⟩,(997321809467339/1000000000000000000)⟩
theorem valid437 : certificate437.Valid := by decide +kernel
theorem sound437 : 0 ≤ cappedLabelEntropy (certificate437.rho:ℝ) ∧ cappedLabelEntropy (certificate437.rho:ℝ) ≤ (certificate437.bound:ℝ) := rat_label_entropy_certificate_sound certificate437 valid437

def certificate438 : RatLabelEntropyCertificate := ⟨(292282037221301/1000000000000000000),⟨(1000000000000000000/292282037221301),11,12,(813779134096392977/100000000000000000)⟩,⟨(1000000000000000000/999707717962778699),0,1,(73081189985217/250000000000000000)⟩,(2670769550283303/1000000000000000000)⟩
theorem valid438 : certificate438.Valid := by decide +kernel
theorem sound438 : 0 ≤ cappedLabelEntropy (certificate438.rho:ℝ) ∧ cappedLabelEntropy (certificate438.rho:ℝ) ≤ (certificate438.bound:ℝ) := rat_label_entropy_certificate_sound certificate438 valid438

def certificate439 : RatLabelEntropyCertificate := ⟨(89504954814692667/1000000000000000000),⟨(1000000000000000000/89504954814692667),3,10,(2413461294175675557/1000000000000000000)⟩,⟨(1000000000000000000/910495045185307333),0,5,(11720852711319793/125000000000000000)⟩,(301390970634231103/1000000000000000000)⟩
theorem valid439 : certificate439.Valid := by decide +kernel
theorem sound439 : 0 ≤ cappedLabelEntropy (certificate439.rho:ℝ) ∧ cappedLabelEntropy (certificate439.rho:ℝ) ≤ (certificate439.bound:ℝ) := rat_label_entropy_certificate_sound certificate439 valid439

end Cycle12.CutLabelCertificates.Entropy021
