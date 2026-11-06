import Cycle12.RationalLabelEntropy
import Cycle12.RationalMinorityBudget

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CutLabelCertificates.Entropy023

def certificate460 : RatLabelEntropyCertificate := ⟨(8213535879365889/1000000000000000000),⟨(1000000000000000000/8213535879365889),6,15,(2400985884325957793/500000000000000000)⟩,⟨(1000000000000000000/991786464120634111),0,3,(8247452811489681/1000000000000000000)⟩,(47620879475433719/1000000000000000000)⟩
theorem valid460 : certificate460.Valid := by decide +kernel
theorem sound460 : 0 ≤ cappedLabelEntropy (certificate460.rho:ℝ) ∧ cappedLabelEntropy (certificate460.rho:ℝ) ≤ (certificate460.bound:ℝ) := rat_label_entropy_certificate_sound certificate460 valid460

def certificate461 : RatLabelEntropyCertificate := ⟨(4614923210029077/50000000000000000),⟨(50000000000000000/4614923210029077),3,9,(2382727776825398283/1000000000000000000)⟩,⟨(50000000000000000/45385076789970923),0,5,(48419829741457707/500000000000000000)⟩,(38477952755998163/125000000000000000)⟩
theorem valid461 : certificate461.Valid := by decide +kernel
theorem sound461 : 0 ≤ cappedLabelEntropy (certificate461.rho:ℝ) ∧ cappedLabelEntropy (certificate461.rho:ℝ) ≤ (certificate461.bound:ℝ) := rat_label_entropy_certificate_sound certificate461 valid461

def certificate462 : RatLabelEntropyCertificate := ⟨(172714650615681/500000000000000000),⟨(500000000000000000/172714650615681),11,10,(7970722563101202859/1000000000000000000)⟩,⟨(500000000000000000/499827285349384319),0,1,(172744487837517/500000000000000000)⟩,(3098690758940683/1000000000000000000)⟩
theorem valid462 : certificate462.Valid := by decide +kernel
theorem sound462 : 0 ≤ cappedLabelEntropy (certificate462.rho:ℝ) ∧ cappedLabelEntropy (certificate462.rho:ℝ) ≤ (certificate462.bound:ℝ) := rat_label_entropy_certificate_sound certificate462 valid462

def certificate463 : RatLabelEntropyCertificate := ⟨(69291569682321/250000000000000000),⟨(250000000000000000/69291569682321),11,14,(8190892947654196941/1000000000000000000)⟩,⟨(250000000000000000/249930708430317679),0,1,(277204696401203/1000000000000000000)⟩,(509473436475661/200000000000000000)⟩
theorem valid463 : certificate463.Valid := by decide +kernel
theorem sound463 : 0 ≤ cappedLabelEntropy (certificate463.rho:ℝ) ∧ cappedLabelEntropy (certificate463.rho:ℝ) ≤ (certificate463.bound:ℝ) := rat_label_entropy_certificate_sound certificate463 valid463

def certificate464 : RatLabelEntropyCertificate := ⟨(244316135699649/500000000000000000),⟨(500000000000000000/244316135699649),10,16,(7623900352612589001/1000000000000000000)⟩,⟨(500000000000000000/499755683864300351),0,1,(24437584552537/50000000000000000)⟩,(421379661742079/100000000000000000)⟩
theorem valid464 : certificate464.Valid := by decide +kernel
theorem sound464 : 0 ≤ cappedLabelEntropy (certificate464.rho:ℝ) ∧ cappedLabelEntropy (certificate464.rho:ℝ) ≤ (certificate464.bound:ℝ) := rat_label_entropy_certificate_sound certificate464 valid464

def certificate465 : RatLabelEntropyCertificate := ⟨(4727513740813279/500000000000000000),⟨(500000000000000000/4727513740813279),6,12,(1165302167576294489/250000000000000000)⟩,⟨(500000000000000000/495272486259186721),0,3,(4750005009629677/500000000000000000)⟩,(53482043238782973/1000000000000000000)⟩
theorem valid465 : certificate465.Valid := by decide +kernel
theorem sound465 : 0 ≤ cappedLabelEntropy (certificate465.rho:ℝ) ∧ cappedLabelEntropy (certificate465.rho:ℝ) ≤ (certificate465.bound:ℝ) := rat_label_entropy_certificate_sound certificate465 valid465

def certificate466 : RatLabelEntropyCertificate := ⟨(46077955750272969/500000000000000000),⟨(500000000000000000/46077955750272969),3,9,(74508545189904307/31250000000000000)⟩,⟨(500000000000000000/453922044249727031),0,5,(96682623825512311/1000000000000000000)⟩,(61499528238075159/200000000000000000)⟩
theorem valid466 : certificate466.Valid := by decide +kernel
theorem sound466 : 0 ≤ cappedLabelEntropy (certificate466.rho:ℝ) ∧ cappedLabelEntropy (certificate466.rho:ℝ) ≤ (certificate466.bound:ℝ) := rat_label_entropy_certificate_sound certificate466 valid466

def certificate467 : RatLabelEntropyCertificate := ⟨(395058010641621/1000000000000000000),⟨(1000000000000000000/395058010641621),11,8,(489779871341407859/62500000000000000)⟩,⟨(1000000000000000000/999604941989358379),0,1,(395136066615943/1000000000000000000)⟩,(436355418867333/125000000000000000)⟩
theorem valid467 : certificate467.Valid := by decide +kernel
theorem sound467 : 0 ≤ cappedLabelEntropy (certificate467.rho:ℝ) ∧ cappedLabelEntropy (certificate467.rho:ℝ) ≤ (certificate467.bound:ℝ) := rat_label_entropy_certificate_sound certificate467 valid467

def certificate468 : RatLabelEntropyCertificate := ⟨(39531690558531/125000000000000000),⟨(125000000000000000/39531690558531),11,11,(4029483186710507131/500000000000000000)⟩,⟨(125000000000000000/124960468309441469),0,1,(316303543160121/1000000000000000000)⟩,(1432440015107643/500000000000000000)⟩
theorem valid468 : certificate468.Valid := by decide +kernel
theorem sound468 : 0 ≤ cappedLabelEntropy (certificate468.rho:ℝ) ∧ cappedLabelEntropy (certificate468.rho:ℝ) ≤ (certificate468.bound:ℝ) := rat_label_entropy_certificate_sound certificate468 valid468

def certificate469 : RatLabelEntropyCertificate := ⟨(133698371332509/250000000000000000),⟨(250000000000000000/133698371332509),10,14,(29428241774678591/3906250000000000)⟩,⟨(250000000000000000/249866301628667491),0,1,(267468269185421/500000000000000000)⟩,(4563586646163781/1000000000000000000)⟩
theorem valid469 : certificate469.Valid := by decide +kernel
theorem sound469 : 0 ≤ cappedLabelEntropy (certificate469.rho:ℝ) ∧ cappedLabelEntropy (certificate469.rho:ℝ) ≤ (certificate469.bound:ℝ) := rat_label_entropy_certificate_sound certificate469 valid469

def certificate470 : RatLabelEntropyCertificate := ⟨(5393933268441683/500000000000000000),⟨(500000000000000000/5393933268441683),6,10,(4529333245223211773/1000000000000000000)⟩,⟨(500000000000000000/494606066731558317),0,3,(1355809684360613/125000000000000000)⟩,(29795654837013681/500000000000000000)⟩
theorem valid470 : certificate470.Valid := by decide +kernel
theorem sound470 : 0 ≤ cappedLabelEntropy (certificate470.rho:ℝ) ∧ cappedLabelEntropy (certificate470.rho:ℝ) ≤ (certificate470.bound:ℝ) := rat_label_entropy_certificate_sound certificate470 valid470

def certificate471 : RatLabelEntropyCertificate := ⟨(92014810853985763/1000000000000000000),⟨(1000000000000000000/92014810853985763),3,9,(1192902863673438591/500000000000000000)⟩,⟨(1000000000000000000/907985189146014237),0,6,(24131803006769529/250000000000000000)⟩,(38396842700790347/125000000000000000)⟩
theorem valid471 : certificate471.Valid := by decide +kernel
theorem sound471 : 0 ≤ cappedLabelEntropy (certificate471.rho:ℝ) ∧ cappedLabelEntropy (certificate471.rho:ℝ) ≤ (certificate471.bound:ℝ) := rat_label_entropy_certificate_sound certificate471 valid471

def certificate472 : RatLabelEntropyCertificate := ⟨(111231211617983/250000000000000000),⟨(250000000000000000/111231211617983),11,5,(7717605174393335731/1000000000000000000)⟩,⟨(250000000000000000/249888768788382017),0,2,(89004770980013/200000000000000000)⟩,(3878580150077691/1000000000000000000)⟩
theorem valid472 : certificate472.Valid := by decide +kernel
theorem sound472 : 0 ≤ cappedLabelEntropy (certificate472.rho:ℝ) ∧ cappedLabelEntropy (certificate472.rho:ℝ) ≤ (certificate472.bound:ℝ) := rat_label_entropy_certificate_sound certificate472 valid472

def certificate473 : RatLabelEntropyCertificate := ⟨(358049808000219/1000000000000000000),⟨(1000000000000000000/358049808000219),11,9,(7934838452748813033/1000000000000000000)⟩,⟨(1000000000000000000/999641950191999781),0,1,(22382120196091/62500000000000000)⟩,(1599526542517751/500000000000000000)⟩
theorem valid473 : certificate473.Valid := by decide +kernel
theorem sound473 : 0 ≤ cappedLabelEntropy (certificate473.rho:ℝ) ∧ cappedLabelEntropy (certificate473.rho:ℝ) ≤ (certificate473.bound:ℝ) := rat_label_entropy_certificate_sound certificate473 valid473

def certificate474 : RatLabelEntropyCertificate := ⟨(290655873374817/500000000000000000),⟨(500000000000000000/290655873374817),10,13,(7450223375737705391/1000000000000000000)⟩,⟨(500000000000000000/499709344126625183),0,2,(290740386965627/500000000000000000)⟩,(49120451165519/10000000000000000)⟩
theorem valid474 : certificate474.Valid := by decide +kernel
theorem sound474 : 0 ≤ cappedLabelEntropy (certificate474.rho:ℝ) ∧ cappedLabelEntropy (certificate474.rho:ℝ) ≤ (certificate474.bound:ℝ) := rat_label_entropy_certificate_sound certificate474 valid474

def certificate475 : RatLabelEntropyCertificate := ⟨(12213062753276611/1000000000000000000),⟨(1000000000000000000/12213062753276611),6,8,(881049836514071637/200000000000000000)⟩,⟨(1000000000000000000/987786937246723389),0,3,(12288255050191317/1000000000000000000)⟩,(65939762530687341/1000000000000000000)⟩
theorem valid475 : certificate475.Valid := by decide +kernel
theorem sound475 : 0 ≤ cappedLabelEntropy (certificate475.rho:ℝ) ∧ cappedLabelEntropy (certificate475.rho:ℝ) ≤ (certificate475.bound:ℝ) := rat_label_entropy_certificate_sound certificate475 valid475

def certificate476 : RatLabelEntropyCertificate := ⟨(91876571926726731/1000000000000000000),⟨(1000000000000000000/91876571926726731),3,9,(1193654606094475539/500000000000000000)⟩,⟨(1000000000000000000/908123428073273269),0,5,(96374975617630669/1000000000000000000)⟩,(153429079891688191/500000000000000000)⟩
theorem valid476 : certificate476.Valid := by decide +kernel
theorem sound476 : 0 ≤ cappedLabelEntropy (certificate476.rho:ℝ) ∧ cappedLabelEntropy (certificate476.rho:ℝ) ≤ (certificate476.bound:ℝ) := rat_label_entropy_certificate_sound certificate476 valid476

def certificate477 : RatLabelEntropyCertificate := ⟨(500497588714269/1000000000000000000),⟨(1000000000000000000/500497588714269),10,15,(7599907776974312533/1000000000000000000)⟩,⟨(1000000000000000000/999499502411285731),0,1,(100124575887861/200000000000000000)⟩,(860821567144351/200000000000000000)⟩
theorem valid477 : certificate477.Valid := by decide +kernel
theorem sound477 : 0 ≤ cappedLabelEntropy (certificate477.rho:ℝ) ∧ cappedLabelEntropy (certificate477.rho:ℝ) ≤ (certificate477.bound:ℝ) := rat_label_entropy_certificate_sound certificate477 valid477

def certificate478 : RatLabelEntropyCertificate := ⟨(201289370906627/500000000000000000),⟨(500000000000000000/201289370906627),11,7,(7817619848404896523/1000000000000000000)⟩,⟨(500000000000000000/499798710629093373),0,1,(402659798390101/1000000000000000000)⟩,(887426314665063/250000000000000000)⟩
theorem valid478 : certificate478.Valid := by decide +kernel
theorem sound478 : 0 ≤ cappedLabelEntropy (certificate478.rho:ℝ) ∧ cappedLabelEntropy (certificate478.rho:ℝ) ≤ (certificate478.bound:ℝ) := rat_label_entropy_certificate_sound certificate478 valid478

def certificate479 : RatLabelEntropyCertificate := ⟨(157952049277933/250000000000000000),⟨(250000000000000000/157952049277933),10,11,(7366924695461188151/1000000000000000000)⟩,⟨(250000000000000000/249842047950722067),0,2,(632007872019293/1000000000000000000)⟩,(5286091974362341/1000000000000000000)⟩
theorem valid479 : certificate479.Valid := by decide +kernel
theorem sound479 : 0 ≤ cappedLabelEntropy (certificate479.rho:ℝ) ∧ cappedLabelEntropy (certificate479.rho:ℝ) ≤ (certificate479.bound:ℝ) := rat_label_entropy_certificate_sound certificate479 valid479

end Cycle12.CutLabelCertificates.Entropy023
