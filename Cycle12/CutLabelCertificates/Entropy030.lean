import Cycle12.RationalLabelEntropy
import Cycle12.RationalMinorityBudget

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CutLabelCertificates.Entropy030

def certificate600 : RatLabelEntropyCertificate := ⟨(10403921508887297/1000000000000000000),⟨(1000000000000000000/10403921508887297),6,11,(4565572475744903949/1000000000000000000)⟩,⟨(1000000000000000000/989596078491112703),0,3,(5229210316449079/500000000000000000)⟩,(7231183715789099/125000000000000000)⟩
theorem valid600 : certificate600.Valid := by decide +kernel
theorem sound600 : 0 ≤ cappedLabelEntropy (certificate600.rho:ℝ) ∧ cappedLabelEntropy (certificate600.rho:ℝ) ≤ (certificate600.bound:ℝ) := rat_label_entropy_certificate_sound certificate600 valid600

def certificate601 : RatLabelEntropyCertificate := ⟨(23866294179556373/250000000000000000),⟨(250000000000000000/23866294179556373),3,9,(2348993739687374661/1000000000000000000)⟩,⟨(250000000000000000/226133705820443627),0,5,(100334474852765197/1000000000000000000)⟩,(19687695559329763/62500000000000000)⟩
theorem valid601 : certificate601.Valid := by decide +kernel
theorem sound601 : 0 ≤ cappedLabelEntropy (certificate601.rho:ℝ) ∧ cappedLabelEntropy (certificate601.rho:ℝ) ≤ (certificate601.bound:ℝ) := rat_label_entropy_certificate_sound certificate601 valid601

def certificate602 : RatLabelEntropyCertificate := ⟨(312309937903303/125000000000000000),⟨(125000000000000000/312309937903303),8,12,(2996036465422636869/500000000000000000)⟩,⟨(125000000000000000/124687690062096697),0,2,(1250802955868927/500000000000000000)⟩,(17466427100197029/1000000000000000000)⟩
theorem valid602 : certificate602.Valid := by decide +kernel
theorem sound602 : 0 ≤ cappedLabelEntropy (certificate602.rho:ℝ) ∧ cappedLabelEntropy (certificate602.rho:ℝ) ≤ (certificate602.bound:ℝ) := rat_label_entropy_certificate_sound certificate602 valid602

def certificate603 : RatLabelEntropyCertificate := ⟨(402664714011967/200000000000000000),⟨(200000000000000000/402664714011967),8,15,(620796840502331007/100000000000000000)⟩,⟨(200000000000000000/199597335285988033),0,2,(2015353030389771/1000000000000000000)⟩,(14509944584651887/1000000000000000000)⟩
theorem valid603 : certificate603.Valid := by decide +kernel
theorem sound603 : 0 ≤ cappedLabelEntropy (certificate603.rho:ℝ) ∧ cappedLabelEntropy (certificate603.rho:ℝ) ≤ (certificate603.bound:ℝ) := rat_label_entropy_certificate_sound certificate603 valid603

def certificate604 : RatLabelEntropyCertificate := ⟨(1141382550732003/500000000000000000),⟨(500000000000000000/1141382550732003),8,13,(6082367807019766541/1000000000000000000)⟩,⟨(500000000000000000/498858617449267997),0,2,(18282996653559/8000000000000000)⟩,(16164774572488891/1000000000000000000)⟩
theorem valid604 : certificate604.Valid := by decide +kernel
theorem sound604 : 0 ≤ cappedLabelEntropy (certificate604.rho:ℝ) ∧ cappedLabelEntropy (certificate604.rho:ℝ) ≤ (certificate604.bound:ℝ) := rat_label_entropy_certificate_sound certificate604 valid604

def certificate605 : RatLabelEntropyCertificate := ⟨(2616620726771071/250000000000000000),⟨(250000000000000000/2616620726771071),6,11,(4559577231538157153/1000000000000000000)⟩,⟨(250000000000000000/247383379273228929),0,3,(5260820878161367/500000000000000000)⟩,(58134254330150521/1000000000000000000)⟩
theorem valid605 : certificate605.Valid := by decide +kernel
theorem sound605 : 0 ≤ cappedLabelEntropy (certificate605.rho:ℝ) ∧ cappedLabelEntropy (certificate605.rho:ℝ) ≤ (certificate605.bound:ℝ) := rat_label_entropy_certificate_sound certificate605 valid605

def certificate606 : RatLabelEntropyCertificate := ⟨(23856345726350931/250000000000000000),⟨(250000000000000000/23856345726350931),3,8,(2349410667726945303/1000000000000000000)⟩,⟨(250000000000000000/226143654273649069),0,5,(100290482143490619/1000000000000000000)⟩,(314913637053064467/1000000000000000000)⟩
theorem valid606 : certificate606.Valid := by decide +kernel
theorem sound606 : 0 ≤ cappedLabelEntropy (certificate606.rho:ℝ) ∧ cappedLabelEntropy (certificate606.rho:ℝ) ≤ (certificate606.bound:ℝ) := rat_label_entropy_certificate_sound certificate606 valid606

def certificate607 : RatLabelEntropyCertificate := ⟨(2515863671423739/1000000000000000000),⟨(1000000000000000000/2515863671423739),8,11,(5985139126260736457/1000000000000000000)⟩,⟨(1000000000000000000/997484136328576261),0,2,(50380675491563/20000000000000000)⟩,(8785245162596903/500000000000000000)⟩
theorem valid607 : certificate607.Valid := by decide +kernel
theorem sound607 : 0 ≤ cappedLabelEntropy (certificate607.rho:ℝ) ∧ cappedLabelEntropy (certificate607.rho:ℝ) ≤ (certificate607.bound:ℝ) := rat_label_entropy_certificate_sound certificate607 valid607

def certificate608 : RatLabelEntropyCertificate := ⟨(506631649194443/250000000000000000),⟨(250000000000000000/506631649194443),8,15,(775178998436579349/125000000000000000)⟩,⟨(250000000000000000/249493368350805557),0,2,(507145695052853/250000000000000000)⟩,(14591838664015813/1000000000000000000)⟩
theorem valid608 : certificate608.Valid := by decide +kernel
theorem sound608 : 0 ≤ cappedLabelEntropy (certificate608.rho:ℝ) ∧ cappedLabelEntropy (certificate608.rho:ℝ) ≤ (certificate608.bound:ℝ) := rat_label_entropy_certificate_sound certificate608 valid608

def certificate609 : RatLabelEntropyCertificate := ⟨(143630855038469/62500000000000000),⟨(62500000000000000/143630855038469),8,13,(6075675334235269883/1000000000000000000)⟩,⟨(62500000000000000/62356369144961531),0,2,(575184587618561/250000000000000000)⟩,(8128961064643917/500000000000000000)⟩
theorem valid609 : certificate609.Valid := by decide +kernel
theorem sound609 : 0 ≤ cappedLabelEntropy (certificate609.rho:ℝ) ∧ cappedLabelEntropy (certificate609.rho:ℝ) ≤ (certificate609.bound:ℝ) := rat_label_entropy_certificate_sound certificate609 valid609

def certificate610 : RatLabelEntropyCertificate := ⟨(2636592663749347/250000000000000000),⟨(250000000000000000/2636592663749347),6,10,(1137993372997671857/250000000000000000)⟩,⟨(250000000000000000/247363407336250653),0,3,(5301188875548461/500000000000000000)⟩,(5849736080376613/100000000000000000)⟩
theorem valid610 : certificate610.Valid := by decide +kernel
theorem sound610 : 0 ≤ cappedLabelEntropy (certificate610.rho:ℝ) ∧ cappedLabelEntropy (certificate610.rho:ℝ) ≤ (certificate610.bound:ℝ) := rat_label_entropy_certificate_sound certificate610 valid610

def certificate611 : RatLabelEntropyCertificate := ⟨(95381822147135583/1000000000000000000),⟨(1000000000000000000/95381822147135583),3,9,(2349867262214694721/1000000000000000000)⟩,⟨(1000000000000000000/904618177852864417),0,5,(20048465446660563/200000000000000000)⟩,(78703913169864847/250000000000000000)⟩
theorem valid611 : certificate611.Valid := by decide +kernel
theorem sound611 : 0 ≤ cappedLabelEntropy (certificate611.rho:ℝ) ∧ cappedLabelEntropy (certificate611.rho:ℝ) ≤ (certificate611.bound:ℝ) := rat_label_entropy_certificate_sound certificate611 valid611

def certificate612 : RatLabelEntropyCertificate := ⟨(633406332106677/250000000000000000),⟨(250000000000000000/633406332106677),8,11,(2989052032889478283/500000000000000000)⟩,⟨(250000000000000000/249366593667893323),0,2,(1268420194366369/500000000000000000)⟩,(17676688862697917/1000000000000000000)⟩
theorem valid612 : certificate612.Valid := by decide +kernel
theorem sound612 : 0 ≤ cappedLabelEntropy (certificate612.rho:ℝ) ∧ cappedLabelEntropy (certificate612.rho:ℝ) ≤ (certificate612.bound:ℝ) := rat_label_entropy_certificate_sound certificate612 valid612

def certificate613 : RatLabelEntropyCertificate := ⟨(63766470377623/31250000000000000),⟨(31250000000000000/63766470377623),8,15,(6194547145630241687/1000000000000000000)⟩,⟨(31250000000000000/31186233529622377),0,2,(2042611763832319/1000000000000000000)⟩,(917411549083697/62500000000000000)⟩
theorem valid613 : certificate613.Valid := by decide +kernel
theorem sound613 : 0 ≤ cappedLabelEntropy (certificate613.rho:ℝ) ∧ cappedLabelEntropy (certificate613.rho:ℝ) ≤ (certificate613.bound:ℝ) := rat_label_entropy_certificate_sound certificate613 valid613

def certificate614 : RatLabelEntropyCertificate := ⟨(462827366069623/200000000000000000),⟨(200000000000000000/462827366069623),8,12,(6068718520434169543/1000000000000000000)⟩,⟨(200000000000000000/199537172633930377),0,2,(2316818583076917/1000000000000000000)⟩,(2044412773627127/125000000000000000)⟩
theorem valid614 : certificate614.Valid := by decide +kernel
theorem sound614 : 0 ≤ cappedLabelEntropy (certificate614.rho:ℝ) ∧ cappedLabelEntropy (certificate614.rho:ℝ) ≤ (certificate614.bound:ℝ) := rat_label_entropy_certificate_sound certificate614 valid614

def certificate615 : RatLabelEntropyCertificate := ⟨(2656114084103529/250000000000000000),⟨(250000000000000000/2656114084103529),6,10,(454459673381829553/100000000000000000)⟩,⟨(250000000000000000/247343885915896471),0,3,(10681298844966321/1000000000000000000)⟩,(7356460677104309/125000000000000000)⟩
theorem valid615 : certificate615.Valid := by decide +kernel
theorem sound615 : 0 ≤ cappedLabelEntropy (certificate615.rho:ℝ) ∧ cappedLabelEntropy (certificate615.rho:ℝ) ≤ (certificate615.bound:ℝ) := rat_label_entropy_certificate_sound certificate615 valid615

def certificate616 : RatLabelEntropyCertificate := ⟨(5960180630799423/62500000000000000),⟨(62500000000000000/5960180630799423),3,8,(587516442235809879/250000000000000000)⟩,⟨(62500000000000000/56539819369200577),0,6,(100221399225548923/1000000000000000000)⟩,(31477306058082117/100000000000000000)⟩
theorem valid616 : certificate616.Valid := by decide +kernel
theorem sound616 : 0 ≤ cappedLabelEntropy (certificate616.rho:ℝ) ∧ cappedLabelEntropy (certificate616.rho:ℝ) ≤ (certificate616.bound:ℝ) := rat_label_entropy_certificate_sound certificate616 valid616

def certificate617 : RatLabelEntropyCertificate := ⟨(2607526250711463/1000000000000000000),⟨(1000000000000000000/2607526250711463),8,10,(5949353303753075893/1000000000000000000)⟩,⟨(1000000000000000000/997392473749288537),0,2,(522186353711699/200000000000000000)⟩,(4529304652431569/250000000000000000)⟩
theorem valid617 : certificate617.Valid := by decide +kernel
theorem sound617 : 0 ≤ cappedLabelEntropy (certificate617.rho:ℝ) ∧ cappedLabelEntropy (certificate617.rho:ℝ) ≤ (certificate617.bound:ℝ) := rat_label_entropy_certificate_sound certificate617 valid617

def certificate618 : RatLabelEntropyCertificate := ⟨(26291716965489/12500000000000000),⟨(12500000000000000/26291716965489),8,14,(6164229977990023091/1000000000000000000)⟩,⟨(12500000000000000/12473708283034511),0,2,(2105552477900701/1000000000000000000)⟩,(3766644745509/250000000000000)⟩
theorem valid618 : certificate618.Valid := by decide +kernel
theorem sound618 : 0 ≤ cappedLabelEntropy (certificate618.rho:ℝ) ∧ cappedLabelEntropy (certificate618.rho:ℝ) ≤ (certificate618.bound:ℝ) := rat_label_entropy_certificate_sound certificate618 valid618

def certificate619 : RatLabelEntropyCertificate := ⟨(1176158791530631/500000000000000000),⟨(500000000000000000/1176158791530631),8,13,(6052354231249294927/1000000000000000000)⟩,⟨(500000000000000000/498823841208469369),0,2,(2355088628505921/1000000000000000000)⟩,(16586607989198363/1000000000000000000)⟩
theorem valid619 : certificate619.Valid := by decide +kernel
theorem sound619 : 0 ≤ cappedLabelEntropy (certificate619.rho:ℝ) ∧ cappedLabelEntropy (certificate619.rho:ℝ) ≤ (certificate619.bound:ℝ) := rat_label_entropy_certificate_sound certificate619 valid619

end Cycle12.CutLabelCertificates.Entropy030
