import Cycle12.RationalLabelEntropy
import Cycle12.RationalMinorityBudget

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CutLabelCertificates.Entropy010

def certificate200 : RatLabelEntropyCertificate := ⟨(23508387100578811/250000000000000000),⟨(250000000000000000/23508387100578811),3,9,(118205183124403377/50000000000000000)⟩,⟨(250000000000000000/226491612899421189),0,5,(98753002766381617/1000000000000000000)⟩,(311771963675537541/1000000000000000000)⟩
theorem valid200 : certificate200.Valid := by decide +kernel
theorem sound200 : 0 ≤ cappedLabelEntropy (certificate200.rho:ℝ) ∧ cappedLabelEntropy (certificate200.rho:ℝ) ≤ (certificate200.bound:ℝ) := rat_label_entropy_certificate_sound certificate200 valid200

def certificate201 : RatLabelEntropyCertificate := ⟨(386900471175293/3906250000000000),⟨(3906250000000000/386900471175293),3,8,(2312165633957086179/1000000000000000000)⟩,⟨(3906250000000000/3519349528824707),0,6,(104301654916415757/1000000000000000000)⟩,(322982900044554667/1000000000000000000)⟩
theorem valid201 : certificate201.Valid := by decide +kernel
theorem sound201 : 0 ≤ cappedLabelEntropy (certificate201.rho:ℝ) ∧ cappedLabelEntropy (certificate201.rho:ℝ) ≤ (certificate201.bound:ℝ) := rat_label_entropy_certificate_sound certificate201 valid201

def certificate202 : RatLabelEntropyCertificate := ⟨(104744045682349229/1000000000000000000),⟨(1000000000000000000/104744045682349229),3,7,(9024942259693811/4000000000000000)⟩,⟨(1000000000000000000/895255954317650771),0,6,(55322809557326811/500000000000000000)⟩,(67076678082807937/200000000000000000)⟩
theorem valid202 : certificate202.Valid := by decide +kernel
theorem sound202 : 0 ≤ cappedLabelEntropy (certificate202.rho:ℝ) ∧ cappedLabelEntropy (certificate202.rho:ℝ) ≤ (certificate202.bound:ℝ) := rat_label_entropy_certificate_sound certificate202 valid202

def certificate203 : RatLabelEntropyCertificate := ⟨(109753937664947501/1000000000000000000),⟨(1000000000000000000/109753937664947501),3,6,(3535222958678991/1600000000000000)⟩,⟨(1000000000000000000/890246062335052499),0,6,(58128689967112823/500000000000000000)⟩,(34600057485292531/100000000000000000)⟩
theorem valid203 : certificate203.Valid := by decide +kernel
theorem sound203 : 0 ≤ cappedLabelEntropy (certificate203.rho:ℝ) ∧ cappedLabelEntropy (certificate203.rho:ℝ) ≤ (certificate203.bound:ℝ) := rat_label_entropy_certificate_sound certificate203 valid203

def certificate204 : RatLabelEntropyCertificate := ⟨(57598882409397597/500000000000000000),⟨(500000000000000000/57598882409397597),3,5,(1080552466761602201/500000000000000000)⟩,⟨(500000000000000000/442401117590602403),0,6,(15298890252235627/125000000000000000)⟩,(71449279241700871/200000000000000000)⟩
theorem valid204 : certificate204.Valid := by decide +kernel
theorem sound204 : 0 ≤ cappedLabelEntropy (certificate204.rho:ℝ) ∧ cappedLabelEntropy (certificate204.rho:ℝ) ≤ (certificate204.bound:ℝ) := rat_label_entropy_certificate_sound certificate204 valid204

def certificate205 : RatLabelEntropyCertificate := ⟨(24260276544067903/200000000000000000),⟨(200000000000000000/24260276544067903),3,4,(421895412783741217/200000000000000000)⟩,⟨(200000000000000000/175739723455932097),0,6,(129313310079323793/1000000000000000000)⟩,(36950991143273887/100000000000000000)⟩
theorem valid205 : certificate205.Valid := by decide +kernel
theorem sound205 : 0 ≤ cappedLabelEntropy (certificate205.rho:ℝ) ∧ cappedLabelEntropy (certificate205.rho:ℝ) ≤ (certificate205.bound:ℝ) := rat_label_entropy_certificate_sound certificate205 valid205

def certificate206 : RatLabelEntropyCertificate := ⟨(6344922364993061/50000000000000000),⟨(50000000000000000/6344922364993061),2,15,(2064368139956341819/1000000000000000000)⟩,⟨(50000000000000000/43655077635006939),0,6,(27140680758179097/200000000000000000)⟩,(380447964172287121/1000000000000000000)⟩
theorem valid206 : certificate206.Valid := by decide +kernel
theorem sound206 : 0 ≤ cappedLabelEntropy (certificate206.rho:ℝ) ∧ cappedLabelEntropy (certificate206.rho:ℝ) ≤ (certificate206.bound:ℝ) := rat_label_entropy_certificate_sound certificate206 valid206

def certificate207 : RatLabelEntropyCertificate := ⟨(26670208484247813/200000000000000000),⟨(200000000000000000/26670208484247813),2,15,(1007385105601261283/500000000000000000)⟩,⟨(200000000000000000/173329791515752187),0,6,(71560638706204787/500000000000000000)⟩,(196353806889960899/500000000000000000)⟩
theorem valid207 : certificate207.Valid := by decide +kernel
theorem sound207 : 0 ≤ cappedLabelEntropy (certificate207.rho:ℝ) ∧ cappedLabelEntropy (certificate207.rho:ℝ) ≤ (certificate207.bound:ℝ) := rat_label_entropy_certificate_sound certificate207 valid207

def certificate208 : RatLabelEntropyCertificate := ⟨(34732479115612933/250000000000000000),⟨(250000000000000000/34732479115612933),2,15,(1973785671113912533/1000000000000000000)⟩,⟨(250000000000000000/215267520884387067),0,6,(149579380030156703/1000000000000000000)⟩,(403016207660701809/1000000000000000000)⟩
theorem valid208 : certificate208.Valid := by decide +kernel
theorem sound208 : 0 ≤ cappedLabelEntropy (certificate208.rho:ℝ) ∧ cappedLabelEntropy (certificate208.rho:ℝ) ≤ (certificate208.bound:ℝ) := rat_label_entropy_certificate_sound certificate208 valid208

def certificate209 : RatLabelEntropyCertificate := ⟨(72351855915117119/500000000000000000),⟨(500000000000000000/72351855915117119),2,14,(966533496885800373/500000000000000000)⟩,⟨(500000000000000000/427648144084882881),0,7,(31261466840798569/200000000000000000)⟩,(206705525986824533/500000000000000000)⟩
theorem valid209 : certificate209.Valid := by decide +kernel
theorem sound209 : 0 ≤ cappedLabelEntropy (certificate209.rho:ℝ) ∧ cappedLabelEntropy (certificate209.rho:ℝ) ≤ (certificate209.bound:ℝ) := rat_label_entropy_certificate_sound certificate209 valid209

def certificate210 : RatLabelEntropyCertificate := ⟨(30352422058615323/200000000000000000),⟨(200000000000000000/30352422058615323),2,12,(1885441047988981017/1000000000000000000)⟩,⟨(200000000000000000/169647577941384677),0,7,(164594152216737149/1000000000000000000)⟩,(425753508610422941/1000000000000000000)⟩
theorem valid210 : certificate210.Valid := by decide +kernel
theorem sound210 : 0 ≤ cappedLabelEntropy (certificate210.rho:ℝ) ∧ cappedLabelEntropy (certificate210.rho:ℝ) ≤ (certificate210.bound:ℝ) := rat_label_entropy_certificate_sound certificate210 valid210

def certificate211 : RatLabelEntropyCertificate := ⟨(78811530700179971/500000000000000000),⟨(500000000000000000/78811530700179971),2,12,(1847548783580868733/1000000000000000000)⟩,⟨(500000000000000000/421188469299820029),0,7,(21440961796060333/125000000000000000)⟩,(217853634710852371/500000000000000000)⟩
theorem valid211 : certificate211.Valid := by decide +kernel
theorem sound211 : 0 ≤ cappedLabelEntropy (certificate211.rho:ℝ) ∧ cappedLabelEntropy (certificate211.rho:ℝ) ≤ (certificate211.bound:ℝ) := rat_label_entropy_certificate_sound certificate211 valid211

def certificate212 : RatLabelEntropyCertificate := ⟨(165083225210530431/1000000000000000000),⟨(1000000000000000000/165083225210530431),2,11,(1801305537030728141/1000000000000000000)⟩,⟨(1000000000000000000/834916774789469569),0,7,(180423230009571767/1000000000000000000)⟩,(28000231808706841/62500000000000000)⟩
theorem valid212 : certificate212.Valid := by decide +kernel
theorem sound212 : 0 ≤ cappedLabelEntropy (certificate212.rho:ℝ) ∧ cappedLabelEntropy (certificate212.rho:ℝ) ≤ (certificate212.bound:ℝ) := rat_label_entropy_certificate_sound certificate212 valid212

def certificate213 : RatLabelEntropyCertificate := ⟨(171220818922186309/1000000000000000000),⟨(1000000000000000000/171220818922186309),2,10,(441200304203498951/250000000000000000)⟩,⟨(1000000000000000000/828779181077813691),0,7,(187801527148334519/1000000000000000000)⟩,(228908352726461357/500000000000000000)⟩
theorem valid213 : certificate213.Valid := by decide +kernel
theorem sound213 : 0 ≤ cappedLabelEntropy (certificate213.rho:ℝ) ∧ cappedLabelEntropy (certificate213.rho:ℝ) ≤ (certificate213.bound:ℝ) := rat_label_entropy_certificate_sound certificate213 valid213

def certificate214 : RatLabelEntropyCertificate := ⟨(89426194147770609/500000000000000000),⟨(500000000000000000/89426194147770609),2,9,(1721194459742890791/1000000000000000000)⟩,⟨(500000000000000000/410573805852229391),0,7,(615788720873043/3125000000000000)⟩,(469648839833091509/1000000000000000000)⟩
theorem valid214 : certificate214.Valid := by decide +kernel
theorem sound214 : 0 ≤ cappedLabelEntropy (certificate214.rho:ℝ) ∧ cappedLabelEntropy (certificate214.rho:ℝ) ≤ (certificate214.bound:ℝ) := rat_label_entropy_certificate_sound certificate214 valid214

def certificate215 : RatLabelEntropyCertificate := ⟨(92629151562967549/500000000000000000),⟨(500000000000000000/92629151562967549),2,9,(1686004194617748317/1000000000000000000)⟩,⟨(500000000000000000/407370848437032451),0,7,(204884152327054663/1000000000000000000)⟩,(2396369690438209/5000000000000000)⟩
theorem valid215 : certificate215.Valid := by decide +kernel
theorem sound215 : 0 ≤ cappedLabelEntropy (certificate215.rho:ℝ) ∧ cappedLabelEntropy (certificate215.rho:ℝ) ≤ (certificate215.bound:ℝ) := rat_label_entropy_certificate_sound certificate215 valid215

def certificate216 : RatLabelEntropyCertificate := ⟨(193291758248716917/1000000000000000000),⟨(1000000000000000000/193291758248716917),2,8,(821777265388039373/500000000000000000)⟩,⟨(1000000000000000000/806708241751283083),0,8,(214793210466527169/1000000000000000000)⟩,(490960998186918609/1000000000000000000)⟩
theorem valid216 : certificate216.Valid := by decide +kernel
theorem sound216 : 0 ≤ cappedLabelEntropy (certificate216.rho:ℝ) ∧ cappedLabelEntropy (certificate216.rho:ℝ) ≤ (certificate216.bound:ℝ) := rat_label_entropy_certificate_sound certificate216 valid216

def certificate217 : RatLabelEntropyCertificate := ⟨(199885747602405631/1000000000000000000),⟨(1000000000000000000/199885747602405631),2,8,(402502334413592559/250000000000000000)⟩,⟨(1000000000000000000/800114252397594369),0,8,(111500373007189511/500000000000000000)⟩,(500243995285298407/1000000000000000000)⟩
theorem valid217 : certificate217.Valid := by decide +kernel
theorem sound217 : 0 ≤ cappedLabelEntropy (certificate217.rho:ℝ) ∧ cappedLabelEntropy (certificate217.rho:ℝ) ≤ (certificate217.bound:ℝ) := rat_label_entropy_certificate_sound certificate217 valid217

def certificate218 : RatLabelEntropyCertificate := ⟨(103340024888769731/500000000000000000),⟨(500000000000000000/103340024888769731),2,7,(1576583334719658573/1000000000000000000)⟩,⟨(500000000000000000/396659975111230269),0,8,(231528670594504149/1000000000000000000)⟩,(7961322430146917/15625000000000000)⟩
theorem valid218 : certificate218.Valid := by decide +kernel
theorem sound218 : 0 ≤ cappedLabelEntropy (certificate218.rho:ℝ) ∧ cappedLabelEntropy (certificate218.rho:ℝ) ≤ (certificate218.bound:ℝ) := rat_label_entropy_certificate_sound certificate218 valid218

def certificate219 : RatLabelEntropyCertificate := ⟨(214995330401175471/1000000000000000000),⟨(1000000000000000000/214995330401175471),2,6,(768569485077318341/500000000000000000)⟩,⟨(1000000000000000000/785004669598824529),0,8,(60516403170971661/250000000000000000)⟩,(260250168533535089/500000000000000000)⟩
theorem valid219 : certificate219.Valid := by decide +kernel
theorem sound219 : 0 ≤ cappedLabelEntropy (certificate219.rho:ℝ) ∧ cappedLabelEntropy (certificate219.rho:ℝ) ≤ (certificate219.bound:ℝ) := rat_label_entropy_certificate_sound certificate219 valid219

end Cycle12.CutLabelCertificates.Entropy010
