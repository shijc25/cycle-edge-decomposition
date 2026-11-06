import Cycle12.RationalLabelEntropy
import Cycle12.RationalMinorityBudget

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CutLabelCertificates.Entropy034

def certificate680 : RatLabelEntropyCertificate := ⟨(2854988673672681/1000000000000000000),⟨(1000000000000000000/2854988673672681),8,9,(1464671850767996737/250000000000000000)⟩,⟨(1000000000000000000/997145011326327319),0,2,(2859071927450117/1000000000000000000)⟩,(2447174435979921/125000000000000000)⟩
theorem valid680 : certificate680.Valid := by decide +kernel
theorem sound680 : 0 ≤ cappedLabelEntropy (certificate680.rho:ℝ) ∧ cappedLabelEntropy (certificate680.rho:ℝ) ≤ (certificate680.bound:ℝ) := rat_label_entropy_certificate_sound certificate680 valid680

def certificate681 : RatLabelEntropyCertificate := ⟨(3130855312341871/1000000000000000000),⟨(1000000000000000000/3130855312341871),8,7,(576644904903050213/100000000000000000)⟩,⟨(1000000000000000000/996869144687658129),0,2,(3135766693730687/1000000000000000000)⟩,(10589933350212617/500000000000000000)⟩
theorem valid681 : certificate681.Valid := by decide +kernel
theorem sound681 : 0 ≤ cappedLabelEntropy (certificate681.rho:ℝ) ∧ cappedLabelEntropy (certificate681.rho:ℝ) ≤ (certificate681.bound:ℝ) := rat_label_entropy_certificate_sound certificate681 valid681

def certificate682 : RatLabelEntropyCertificate := ⟨(8831503035113491/1000000000000000000),⟨(1000000000000000000/8831503035113491),6,13,(591178757462469219/125000000000000000)⟩,⟨(1000000000000000000/991168496964886509),0,3,(8870731895362371/1000000000000000000)⟩,(10112073185260031/200000000000000000)⟩
theorem valid682 : certificate682.Valid := by decide +kernel
theorem sound682 : 0 ≤ cappedLabelEntropy (certificate682.rho:ℝ) ∧ cappedLabelEntropy (certificate682.rho:ℝ) ≤ (certificate682.bound:ℝ) := rat_label_entropy_certificate_sound certificate682 valid682

def certificate683 : RatLabelEntropyCertificate := ⟨(45780929563488113/500000000000000000),⟨(500000000000000000/45780929563488113),3,9,(2390740479091068583/1000000000000000000)⟩,⟨(500000000000000000/454219070436511887),0,5,(96028482761810003/1000000000000000000)⟩,(76534144826672991/250000000000000000)⟩
theorem valid683 : certificate683.Valid := by decide +kernel
theorem sound683 : 0 ≤ cappedLabelEntropy (certificate683.rho:ℝ) ∧ cappedLabelEntropy (certificate683.rho:ℝ) ≤ (certificate683.bound:ℝ) := rat_label_entropy_certificate_sound certificate683 valid683

def certificate684 : RatLabelEntropyCertificate := ⟨(96582846652431163/1000000000000000000),⟨(1000000000000000000/96582846652431163),3,9,(2337354124417046851/1000000000000000000)⟩,⟨(1000000000000000000/903417153347568837),0,5,(12696358549692629/125000000000000000)⟩,(158754589880873103/500000000000000000)⟩
theorem valid684 : certificate684.Valid := by decide +kernel
theorem sound684 : 0 ≤ cappedLabelEntropy (certificate684.rho:ℝ) ∧ cappedLabelEntropy (certificate684.rho:ℝ) ≤ (certificate684.bound:ℝ) := rat_label_entropy_certificate_sound certificate684 valid684

def certificate685 : RatLabelEntropyCertificate := ⟨(359984277775627/100000000000000000),⟨(100000000000000000/359984277775627),8,5,(2813432553659619887/500000000000000000)⟩,⟨(100000000000000000/99640015722224373),0,2,(225396112739711/62500000000000000)⟩,(4769837054546003/200000000000000000)⟩
theorem valid685 : certificate685.Valid := by decide +kernel
theorem sound685 : 0 ≤ cappedLabelEntropy (certificate685.rho:ℝ) ∧ cappedLabelEntropy (certificate685.rho:ℝ) ≤ (certificate685.bound:ℝ) := rat_label_entropy_certificate_sound certificate685 valid685

def certificate686 : RatLabelEntropyCertificate := ⟨(2923166202363739/1000000000000000000),⟨(1000000000000000000/2923166202363739),8,9,(2917543967134901303/500000000000000000)⟩,⟨(1000000000000000000/997076833797636261),0,2,(182965437314913/62500000000000000)⟩,(4993955355048897/250000000000000000)⟩
theorem valid686 : certificate686.Valid := by decide +kernel
theorem sound686 : 0 ≤ cappedLabelEntropy (certificate686.rho:ℝ) ∧ cappedLabelEntropy (certificate686.rho:ℝ) ≤ (certificate686.bound:ℝ) := rat_label_entropy_certificate_sound certificate686 valid686

def certificate687 : RatLabelEntropyCertificate := ⟨(641275648716179/200000000000000000),⟨(200000000000000000/641275648716179),8,7,(5742613251847153069/1000000000000000000)⟩,⟨(200000000000000000/199358724351283821),0,2,(321152968890349/100000000000000000)⟩,(21614222502002423/1000000000000000000)⟩
theorem valid687 : certificate687.Valid := by decide +kernel
theorem sound687 : 0 ≤ cappedLabelEntropy (certificate687.rho:ℝ) ∧ cappedLabelEntropy (certificate687.rho:ℝ) ≤ (certificate687.bound:ℝ) := rat_label_entropy_certificate_sound certificate687 valid687

def certificate688 : RatLabelEntropyCertificate := ⟨(4493303784137149/500000000000000000),⟨(500000000000000000/4493303784137149),6,14,(235600992892918439/50000000000000000)⟩,⟨(500000000000000000/495506696215862851),0,3,(4513615342606587/500000000000000000)⟩,(51291179822105679/1000000000000000000)⟩
theorem valid688 : certificate688.Valid := by decide +kernel
theorem sound688 : 0 ≤ cappedLabelEntropy (certificate688.rho:ℝ) ∧ cappedLabelEntropy (certificate688.rho:ℝ) ≤ (certificate688.bound:ℝ) := rat_label_entropy_certificate_sound certificate688 valid688

def certificate689 : RatLabelEntropyCertificate := ⟨(46087391705048549/500000000000000000),⟨(500000000000000000/46087391705048549),3,9,(238406868463309641/100000000000000000)⟩,⟨(500000000000000000/453912608294951451),0,5,(3021981614135851/31250000000000000)⟩,(76885202567281353/250000000000000000)⟩
theorem valid689 : certificate689.Valid := by decide +kernel
theorem sound689 : 0 ≤ cappedLabelEntropy (certificate689.rho:ℝ) ∧ cappedLabelEntropy (certificate689.rho:ℝ) ≤ (certificate689.bound:ℝ) := rat_label_entropy_certificate_sound certificate689 valid689

def certificate690 : RatLabelEntropyCertificate := ⟨(12063409860713541/125000000000000000),⟨(125000000000000000/12063409860713541),3,9,(93525473784574679/40000000000000000)⟩,⟨(125000000000000000/112936590139286459),0,5,(1268590316286967/12500000000000000)⟩,(317340193883456931/1000000000000000000)⟩
theorem valid690 : certificate690.Valid := by decide +kernel
theorem sound690 : 0 ≤ cappedLabelEntropy (certificate690.rho:ℝ) ∧ cappedLabelEntropy (certificate690.rho:ℝ) ≤ (certificate690.bound:ℝ) := rat_label_entropy_certificate_sound certificate690 valid690

def certificate691 : RatLabelEntropyCertificate := ⟨(3687794055610639/1000000000000000000),⟨(1000000000000000000/3687794055610639),8,5,(1400681704150290897/250000000000000000)⟩,⟨(1000000000000000000/996312205944389361),0,2,(3694610732269177/1000000000000000000)⟩,(2434268841824501/100000000000000000)⟩
theorem valid691 : certificate691.Valid := by decide +kernel
theorem sound691 : 0 ≤ cappedLabelEntropy (certificate691.rho:ℝ) ∧ cappedLabelEntropy (certificate691.rho:ℝ) ≤ (certificate691.bound:ℝ) := rat_label_entropy_certificate_sound certificate691 valid691

def certificate692 : RatLabelEntropyCertificate := ⟨(1496150303637231/500000000000000000),⟨(500000000000000000/1496150303637231),8,8,(5811712753570970749/1000000000000000000)⟩,⟨(500000000000000000/498503849696362769),0,2,(149839324485539/50000000000000000)⟩,(20378210805492899/1000000000000000000)⟩
theorem valid692 : certificate692.Valid := by decide +kernel
theorem sound692 : 0 ≤ cappedLabelEntropy (certificate692.rho:ℝ) ∧ cappedLabelEntropy (certificate692.rho:ℝ) ≤ (certificate692.bound:ℝ) := rat_label_entropy_certificate_sound certificate692 valid692

def certificate693 : RatLabelEntropyCertificate := ⟨(102135955983227/31250000000000000),⟨(31250000000000000/102135955983227),8,7,(5723469827608964419/1000000000000000000)⟩,⟨(31250000000000000/31147864044016773),0,2,(3273703315492249/1000000000000000000)⟩,(2196930970161269/100000000000000000)⟩
theorem valid693 : certificate693.Valid := by decide +kernel
theorem sound693 : 0 ≤ cappedLabelEntropy (certificate693.rho:ℝ) ∧ cappedLabelEntropy (certificate693.rho:ℝ) ≤ (certificate693.bound:ℝ) := rat_label_entropy_certificate_sound certificate693 valid693

def certificate694 : RatLabelEntropyCertificate := ⟨(2214029090685509/250000000000000000),⟨(250000000000000000/2214029090685509),6,14,(1181661736059443409/250000000000000000)⟩,⟨(250000000000000000/247785970909314491),0,3,(1779112968167243/200000000000000000)⟩,(12669130006815561/250000000000000000)⟩
theorem valid694 : certificate694.Valid := by decide +kernel
theorem sound694 : 0 ≤ cappedLabelEntropy (certificate694.rho:ℝ) ∧ cappedLabelEntropy (certificate694.rho:ℝ) ≤ (certificate694.bound:ℝ) := rat_label_entropy_certificate_sound certificate694 valid694

def certificate695 : RatLabelEntropyCertificate := ⟨(90096468837862677/1000000000000000000),⟨(1000000000000000000/90096468837862677),3,9,(2406874306724504733/1000000000000000000)⟩,⟨(1000000000000000000/909903531162137323),0,5,(47208347401302497/500000000000000000)⟩,(151380479987002389/500000000000000000)⟩
theorem valid695 : certificate695.Valid := by decide +kernel
theorem sound695 : 0 ≤ cappedLabelEntropy (certificate695.rho:ℝ) ∧ cappedLabelEntropy (certificate695.rho:ℝ) ≤ (certificate695.bound:ℝ) := rat_label_entropy_certificate_sound certificate695 valid695

def certificate696 : RatLabelEntropyCertificate := ⟨(9643338041116223/100000000000000000),⟨(100000000000000000/9643338041116223),3,8,(93556114699114511/40000000000000000)⟩,⟨(100000000000000000/90356661958883777),0,6,(101405436650063937/1000000000000000000)⟩,(317174877566079211/1000000000000000000)⟩
theorem valid696 : certificate696.Valid := by decide +kernel
theorem sound696 : 0 ≤ cappedLabelEntropy (certificate696.rho:ℝ) ∧ cappedLabelEntropy (certificate696.rho:ℝ) ≤ (certificate696.bound:ℝ) := rat_label_entropy_certificate_sound certificate696 valid696

def certificate697 : RatLabelEntropyCertificate := ⟨(1888523546672771/500000000000000000),⟨(500000000000000000/1888523546672771),8,4,(2789406383438464373/500000000000000000)⟩,⟨(500000000000000000/498111476453327229),0,2,(3784198147977379/1000000000000000000)⟩,(12420671799406711/500000000000000000)⟩
theorem valid697 : certificate697.Valid := by decide +kernel
theorem sound697 : 0 ≤ cappedLabelEntropy (certificate697.rho:ℝ) ∧ cappedLabelEntropy (certificate697.rho:ℝ) ≤ (certificate697.bound:ℝ) := rat_label_entropy_certificate_sound certificate697 valid697

def certificate698 : RatLabelEntropyCertificate := ⟨(382799501483091/125000000000000000),⟨(125000000000000000/382799501483091),8,8,(2894278829498631411/500000000000000000)⟩,⟨(125000000000000000/124617200498516909),0,2,(306709474189833/100000000000000000)⟩,(10392278986277487/500000000000000000)⟩
theorem valid698 : certificate698.Valid := by decide +kernel
theorem sound698 : 0 ≤ cappedLabelEntropy (certificate698.rho:ℝ) ∧ cappedLabelEntropy (certificate698.rho:ℝ) ≤ (certificate698.bound:ℝ) := rat_label_entropy_certificate_sound certificate698 valid698

def certificate699 : RatLabelEntropyCertificate := ⟨(836417804873669/250000000000000000),⟨(250000000000000000/836417804873669),8,6,(5700087942006116151/1000000000000000000)⟩,⟨(250000000000000000/249163582195126331),0,2,(3351280492131601/1000000000000000000)⟩,(22410688385599123/1000000000000000000)⟩
theorem valid699 : certificate699.Valid := by decide +kernel
theorem sound699 : 0 ≤ cappedLabelEntropy (certificate699.rho:ℝ) ∧ cappedLabelEntropy (certificate699.rho:ℝ) ≤ (certificate699.bound:ℝ) := rat_label_entropy_certificate_sound certificate699 valid699

end Cycle12.CutLabelCertificates.Entropy034
