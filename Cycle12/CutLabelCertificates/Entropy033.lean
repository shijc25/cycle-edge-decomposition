import Cycle12.RationalLabelEntropy
import Cycle12.RationalMinorityBudget

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CutLabelCertificates.Entropy033

def certificate660 : RatLabelEntropyCertificate := ⟨(2356268662747003/250000000000000000),⟨(250000000000000000/2356268662747003),6,12,(291523851571887361/62500000000000000)⟩,⟨(250000000000000000/247643731337252997),0,3,(4734885868848207/500000000000000000)⟩,(26671331724939103/500000000000000000)⟩
theorem valid660 : certificate660.Valid := by decide +kernel
theorem sound660 : 0 ≤ cappedLabelEntropy (certificate660.rho:ℝ) ∧ cappedLabelEntropy (certificate660.rho:ℝ) ≤ (certificate660.bound:ℝ) := rat_label_entropy_certificate_sound certificate660 valid660

def certificate661 : RatLabelEntropyCertificate := ⟨(95995909305983271/1000000000000000000),⟨(1000000000000000000/95995909305983271),3,8,(1171724849909099867/500000000000000000)⟩,⟨(1000000000000000000/904004090694016729),0,5,(50460696748099001/500000000000000000)⟩,(2470272948484259/7812500000000000)⟩
theorem valid661 : certificate661.Valid := by decide +kernel
theorem sound661 : 0 ≤ cappedLabelEntropy (certificate661.rho:ℝ) ∧ cappedLabelEntropy (certificate661.rho:ℝ) ≤ (certificate661.bound:ℝ) := rat_label_entropy_certificate_sound certificate661 valid661

def certificate662 : RatLabelEntropyCertificate := ⟨(3319173971121763/1000000000000000000),⟨(1000000000000000000/3319173971121763),8,7,(5708039330889546917/1000000000000000000)⟩,⟨(1000000000000000000/996680826028878237),0,2,(415586831061383/125000000000000000)⟩,(11129817490889867/500000000000000000)⟩
theorem valid662 : certificate662.Valid := by decide +kernel
theorem sound662 : 0 ≤ cappedLabelEntropy (certificate662.rho:ℝ) ∧ cappedLabelEntropy (certificate662.rho:ℝ) ≤ (certificate662.bound:ℝ) := rat_label_entropy_certificate_sound certificate662 valid662

def certificate663 : RatLabelEntropyCertificate := ⟨(2649935461637793/1000000000000000000),⟨(1000000000000000000/2649935461637793),8,11,(1483304998344879533/250000000000000000)⟩,⟨(1000000000000000000/997350064538362207),0,2,(2653452755722207/1000000000000000000)⟩,(734762853572951/40000000000000000)⟩
theorem valid663 : certificate663.Valid := by decide +kernel
theorem sound663 : 0 ≤ cappedLabelEntropy (certificate663.rho:ℝ) ∧ cappedLabelEntropy (certificate663.rho:ℝ) ≤ (certificate663.bound:ℝ) := rat_label_entropy_certificate_sound certificate663 valid663

def certificate664 : RatLabelEntropyCertificate := ⟨(732654938172003/250000000000000000),⟨(250000000000000000/732654938172003),8,9,(729067669828944397/125000000000000000)⟩,⟨(250000000000000000/249267345061827997),0,2,(2934922427146803/1000000000000000000)⟩,(2001928219948461/100000000000000000)⟩
theorem valid664 : certificate664.Valid := by decide +kernel
theorem sound664 : 0 ≤ cappedLabelEntropy (certificate664.rho:ℝ) ∧ cappedLabelEntropy (certificate664.rho:ℝ) ≤ (certificate664.bound:ℝ) := rat_label_entropy_certificate_sound certificate664 valid664

def certificate665 : RatLabelEntropyCertificate := ⟨(189060564273403/20000000000000000),⟨(20000000000000000/189060564273403),6,12,(932284028583456657/200000000000000000)⟩,⟨(20000000000000000/19810939435726597),0,3,(9497991669770673/1000000000000000000)⟩,(53472743013310549/1000000000000000000)⟩
theorem valid665 : certificate665.Valid := by decide +kernel
theorem sound665 : 0 ≤ cappedLabelEntropy (certificate665.rho:ℝ) ∧ cappedLabelEntropy (certificate665.rho:ℝ) ≤ (certificate665.bound:ℝ) := rat_label_entropy_certificate_sound certificate665 valid665

def certificate666 : RatLabelEntropyCertificate := ⟨(47934061892074861/500000000000000000),⟨(500000000000000000/47934061892074861),3,8,(2344781742501447967/1000000000000000000)⟩,⟨(500000000000000000/452065938107925139),0,5,(50390024229889719/500000000000000000)⟩,(315908280636007789/1000000000000000000)⟩
theorem valid666 : certificate666.Valid := by decide +kernel
theorem sound666 : 0 ≤ cappedLabelEntropy (certificate666.rho:ℝ) ∧ cappedLabelEntropy (certificate666.rho:ℝ) ≤ (certificate666.bound:ℝ) := rat_label_entropy_certificate_sound certificate666 valid666

def certificate667 : RatLabelEntropyCertificate := ⟨(167185410301519/50000000000000000),⟨(50000000000000000/167185410301519),8,6,(228026993861166941/40000000000000000)⟩,⟨(50000000000000000/49832814589698481),0,2,(418663861370317/125000000000000000)⟩,(22399505036902453/1000000000000000000)⟩
theorem valid667 : certificate667.Valid := by decide +kernel
theorem sound667 : 0 ≤ cappedLabelEntropy (certificate667.rho:ℝ) ∧ cappedLabelEntropy (certificate667.rho:ℝ) ≤ (certificate667.bound:ℝ) := rat_label_entropy_certificate_sound certificate667 valid667

def certificate668 : RatLabelEntropyCertificate := ⟨(170092123266019/62500000000000000),⟨(62500000000000000/170092123266019),8,10,(590658164388504353/100000000000000000)⟩,⟨(62500000000000000/62329907876733981),0,2,(681295978771111/250000000000000000)⟩,(1879237560682993/100000000000000000)⟩
theorem valid668 : certificate668.Valid := by decide +kernel
theorem sound668 : 0 ≤ cappedLabelEntropy (certificate668.rho:ℝ) ∧ cappedLabelEntropy (certificate668.rho:ℝ) ≤ (certificate668.bound:ℝ) := rat_label_entropy_certificate_sound certificate668 valid668

def certificate669 : RatLabelEntropyCertificate := ⟨(745756069774879/250000000000000000),⟨(250000000000000000/745756069774879),8,8,(581481763432759771/100000000000000000)⟩,⟨(250000000000000000/249254243930225121),0,2,(2987482363948661/1000000000000000000)⟩,(2540539101657357/125000000000000000)⟩
theorem valid669 : certificate669.Valid := by decide +kernel
theorem sound669 : 0 ≤ cappedLabelEntropy (certificate669.rho:ℝ) ∧ cappedLabelEntropy (certificate669.rho:ℝ) ≤ (certificate669.bound:ℝ) := rat_label_entropy_certificate_sound certificate669 valid669

def certificate670 : RatLabelEntropyCertificate := ⟨(8523208594870839/1000000000000000000),⟨(1000000000000000000/8523208594870839),6,14,(190598496535725433/40000000000000000)⟩,⟨(1000000000000000000/991476791405129161),0,3,(106996735692137/12500000000000000)⟩,(12274887752914471/250000000000000000)⟩
theorem valid670 : certificate670.Valid := by decide +kernel
theorem sound670 : 0 ≤ cappedLabelEntropy (certificate670.rho:ℝ) ∧ cappedLabelEntropy (certificate670.rho:ℝ) ≤ (certificate670.bound:ℝ) := rat_label_entropy_certificate_sound certificate670 valid670

def certificate671 : RatLabelEntropyCertificate := ⟨(89405627733455157/1000000000000000000),⟨(1000000000000000000/89405627733455157),3,10,(1207285824372645421/500000000000000000)⟩,⟨(1000000000000000000/910594372266544843),0,5,(3746309453925713/40000000000000000)⟩,(60232100320263839/200000000000000000)⟩
theorem valid671 : certificate671.Valid := by decide +kernel
theorem sound671 : 0 ≤ cappedLabelEntropy (certificate671.rho:ℝ) ∧ cappedLabelEntropy (certificate671.rho:ℝ) ≤ (certificate671.bound:ℝ) := rat_label_entropy_certificate_sound certificate671 valid671

def certificate672 : RatLabelEntropyCertificate := ⟨(24183554293213581/250000000000000000),⟨(250000000000000000/24183554293213581),3,8,(233578809037572867/100000000000000000)⟩,⟨(250000000000000000/225816445706786419),0,6,(50869217865371059/500000000000000000)⟩,(19865467512381903/62500000000000000)⟩
theorem valid672 : certificate672.Valid := by decide +kernel
theorem sound672 : 0 ≤ cappedLabelEntropy (certificate672.rho:ℝ) ∧ cappedLabelEntropy (certificate672.rho:ℝ) ≤ (certificate672.bound:ℝ) := rat_label_entropy_certificate_sound certificate672 valid672

def certificate673 : RatLabelEntropyCertificate := ⟨(1713904684123549/500000000000000000),⟨(500000000000000000/1713904684123549),8,6,(5675833889989203789/1000000000000000000)⟩,⟨(500000000000000000/498286095315876451),0,2,(3433697766835669/1000000000000000000)⟩,(11438802143091071/500000000000000000)⟩
theorem valid673 : certificate673.Valid := by decide +kernel
theorem sound673 : 0 ≤ cappedLabelEntropy (certificate673.rho:ℝ) ∧ cappedLabelEntropy (certificate673.rho:ℝ) ≤ (certificate673.bound:ℝ) := rat_label_entropy_certificate_sound certificate673 valid673

def certificate674 : RatLabelEntropyCertificate := ⟨(1393879807667661/500000000000000000),⟨(500000000000000000/1393879807667661),8,10,(735314626373305221/125000000000000000)⟩,⟨(500000000000000000/498606120192332339),0,2,(2791652654092601/1000000000000000000)⟩,(1918291355731453/100000000000000000)⟩
theorem valid674 : certificate674.Valid := by decide +kernel
theorem sound674 : 0 ≤ cappedLabelEntropy (certificate674.rho:ℝ) ∧ cappedLabelEntropy (certificate674.rho:ℝ) ≤ (certificate674.bound:ℝ) := rat_label_entropy_certificate_sound certificate674 valid674

def certificate675 : RatLabelEntropyCertificate := ⟨(3056403764080213/1000000000000000000),⟨(1000000000000000000/3056403764080213),8,8,(579051629465117683/100000000000000000)⟩,⟨(1000000000000000000/996943596235919787),0,2,(3061084105172471/1000000000000000000)⟩,(20749883995130921/1000000000000000000)⟩
theorem valid675 : certificate675.Valid := by decide +kernel
theorem sound675 : 0 ≤ cappedLabelEntropy (certificate675.rho:ℝ) ∧ cappedLabelEntropy (certificate675.rho:ℝ) ≤ (certificate675.bound:ℝ) := rat_label_entropy_certificate_sound certificate675 valid675

def certificate676 : RatLabelEntropyCertificate := ⟨(4338490264249387/500000000000000000),⟨(500000000000000000/4338490264249387),6,14,(4747081676209400671/1000000000000000000)⟩,⟨(500000000000000000/495661509735750613),0,3,(871484471436157/100000000000000000)⟩,(6228695181016057/125000000000000000)⟩
theorem valid676 : certificate676.Valid := by decide +kernel
theorem sound676 : 0 ≤ cappedLabelEntropy (certificate676.rho:ℝ) ∧ cappedLabelEntropy (certificate676.rho:ℝ) ≤ (certificate676.bound:ℝ) := rat_label_entropy_certificate_sound certificate676 valid676

def certificate677 : RatLabelEntropyCertificate := ⟨(45465289839826829/500000000000000000),⟨(500000000000000000/45465289839826829),3,9,(479531784850939583/200000000000000000)⟩,⟨(500000000000000000/454534710160173171),0,6,(95333817731317479/1000000000000000000)⟩,(15234278713925441/50000000000000000)⟩
theorem valid677 : certificate677.Valid := by decide +kernel
theorem sound677 : 0 ≤ cappedLabelEntropy (certificate677.rho:ℝ) ∧ cappedLabelEntropy (certificate677.rho:ℝ) ≤ (certificate677.bound:ℝ) := rat_label_entropy_certificate_sound certificate677 valid677

def certificate678 : RatLabelEntropyCertificate := ⟨(96657684596573759/1000000000000000000),⟨(1000000000000000000/96657684596573759),3,8,(292072445869168383/125000000000000000)⟩,⟨(1000000000000000000/903342315403426241),0,5,(50826855287454297/500000000000000000)⟩,(79419117274365801/250000000000000000)⟩
theorem valid678 : certificate678.Valid := by decide +kernel
theorem sound678 : 0 ≤ cappedLabelEntropy (certificate678.rho:ℝ) ∧ cappedLabelEntropy (certificate678.rho:ℝ) ≤ (certificate678.bound:ℝ) := rat_label_entropy_certificate_sound certificate678 valid678

def certificate679 : RatLabelEntropyCertificate := ⟨(3513184410903341/1000000000000000000),⟨(1000000000000000000/3513184410903341),8,5,(5651232413223841033/1000000000000000000)⟩,⟨(1000000000000000000/996486815589096659),0,2,(3519370135232173/1000000000000000000)⟩,(23360827555466543/1000000000000000000)⟩
theorem valid679 : certificate679.Valid := by decide +kernel
theorem sound679 : 0 ≤ cappedLabelEntropy (certificate679.rho:ℝ) ∧ cappedLabelEntropy (certificate679.rho:ℝ) ≤ (certificate679.bound:ℝ) := rat_label_entropy_certificate_sound certificate679 valid679

end Cycle12.CutLabelCertificates.Entropy033
