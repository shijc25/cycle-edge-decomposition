import Cycle12.RationalLabelEntropy
import Cycle12.RationalMinorityBudget

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CutLabelCertificates.Entropy028

def certificate560 : RatLabelEntropyCertificate := ⟨(5711130627414391/500000000000000000),⟨(500000000000000000/5711130627414391),6,9,(4472191086051583431/1000000000000000000)⟩,⟨(500000000000000000/494288869372585609),0,3,(2297599264475809/200000000000000000)⟩,(62439312393487973/1000000000000000000)⟩
theorem valid560 : certificate560.Valid := by decide +kernel
theorem sound560 : 0 ≤ cappedLabelEntropy (certificate560.rho:ℝ) ∧ cappedLabelEntropy (certificate560.rho:ℝ) ≤ (certificate560.bound:ℝ) := rat_label_entropy_certificate_sound certificate560 valid560

def certificate561 : RatLabelEntropyCertificate := ⟨(47624872443958999/500000000000000000),⟨(500000000000000000/47624872443958999),3,8,(1175626471660490867/500000000000000000)⟩,⟨(500000000000000000/452375127556041001),0,5,(100096334568629491/1000000000000000000)⟩,(314518427255041671/1000000000000000000)⟩
theorem valid561 : certificate561.Valid := by decide +kernel
theorem sound561 : 0 ≤ cappedLabelEntropy (certificate561.rho:ℝ) ∧ cappedLabelEntropy (certificate561.rho:ℝ) ≤ (certificate561.bound:ℝ) := rat_label_entropy_certificate_sound certificate561 valid561

def certificate562 : RatLabelEntropyCertificate := ⟨(504125960382493/250000000000000000),⟨(250000000000000000/504125960382493),8,15,(3103195019302164327/500000000000000000)⟩,⟨(250000000000000000/249495874039617507),0,2,(126158732673129/62500000000000000)⟩,(7264839342271899/500000000000000000)⟩
theorem valid562 : certificate562.Valid := by decide +kernel
theorem sound562 : 0 ≤ cappedLabelEntropy (certificate562.rho:ℝ) ∧ cappedLabelEntropy (certificate562.rho:ℝ) ≤ (certificate562.bound:ℝ) := rat_label_entropy_certificate_sound certificate562 valid562

def certificate563 : RatLabelEntropyCertificate := ⟨(1622017808502479/1000000000000000000),⟨(1000000000000000000/1622017808502479),9,7,(3212042172000587147/500000000000000000)⟩,⟨(1000000000000000000/998377982191497521),0,2,(1623334703598877/1000000000000000000)⟩,(240813616701847/20000000000000000)⟩
theorem valid563 : certificate563.Valid := by decide +kernel
theorem sound563 : 0 ≤ cappedLabelEntropy (certificate563.rho:ℝ) ∧ cappedLabelEntropy (certificate563.rho:ℝ) ≤ (certificate563.bound:ℝ) := rat_label_entropy_certificate_sound certificate563 valid563

def certificate564 : RatLabelEntropyCertificate := ⟨(375411997005049/200000000000000000),⟨(200000000000000000/375411997005049),9,4,(6278048563963398237/1000000000000000000)⟩,⟨(200000000000000000/199624588002994951),0,2,(187882386974283/100000000000000000)⟩,(13659570948098923/1000000000000000000)⟩
theorem valid564 : certificate564.Valid := by decide +kernel
theorem sound564 : 0 ≤ cappedLabelEntropy (certificate564.rho:ℝ) ∧ cappedLabelEntropy (certificate564.rho:ℝ) ≤ (certificate564.bound:ℝ) := rat_label_entropy_certificate_sound certificate564 valid564

def certificate565 : RatLabelEntropyCertificate := ⟨(11444556989298019/1000000000000000000),⟨(1000000000000000000/11444556989298019),6,9,(4470241034120742529/1000000000000000000)⟩,⟨(1000000000000000000/988555443010701981),0,3,(2877637480343427/250000000000000000)⟩,(12507749009542747/200000000000000000)⟩
theorem valid565 : certificate565.Valid := by decide +kernel
theorem sound565 : 0 ≤ cappedLabelEntropy (certificate565.rho:ℝ) ∧ cappedLabelEntropy (certificate565.rho:ℝ) ≤ (certificate565.bound:ℝ) := rat_label_entropy_certificate_sound certificate565 valid565

def certificate566 : RatLabelEntropyCertificate := ⟨(95098979634444199/1000000000000000000),⟨(1000000000000000000/95098979634444199),3,9,(73526157465134777/31250000000000000)⟩,⟨(1000000000000000000/904901020365555801),0,5,(49964855512668123/500000000000000000)⟩,(78544724778921791/250000000000000000)⟩
theorem valid566 : certificate566.Valid := by decide +kernel
theorem sound566 : 0 ≤ cappedLabelEntropy (certificate566.rho:ℝ) ∧ cappedLabelEntropy (certificate566.rho:ℝ) ≤ (certificate566.bound:ℝ) := rat_label_entropy_certificate_sound certificate566 valid566

def certificate567 : RatLabelEntropyCertificate := ⟨(1039335202394133/500000000000000000),⟨(500000000000000000/1039335202394133),8,14,(3088013409064857169/500000000000000000)⟩,⟨(500000000000000000/498960664797605867),0,2,(2080833838678043/1000000000000000000)⟩,(14914432636985181/1000000000000000000)⟩
theorem valid567 : certificate567.Valid := by decide +kernel
theorem sound567 : 0 ≤ cappedLabelEntropy (certificate567.rho:ℝ) ∧ cappedLabelEntropy (certificate567.rho:ℝ) ≤ (certificate567.bound:ℝ) := rat_label_entropy_certificate_sound certificate567 valid567

def certificate568 : RatLabelEntropyCertificate := ⟨(417337746017449/250000000000000000),⟨(250000000000000000/417337746017449),9,7,(6395320360384109837/1000000000000000000)⟩,⟨(250000000000000000/249582662253982551),0,2,(8353729515231/5000000000000000)⟩,(3085997794694409/250000000000000000)⟩
theorem valid568 : certificate568.Valid := by decide +kernel
theorem sound568 : 0 ≤ cappedLabelEntropy (certificate568.rho:ℝ) ∧ cappedLabelEntropy (certificate568.rho:ℝ) ≤ (certificate568.bound:ℝ) := rat_label_entropy_certificate_sound certificate568 valid568

def certificate569 : RatLabelEntropyCertificate := ⟨(1933196386962017/1000000000000000000),⟨(1000000000000000000/1933196386962017),9,3,(781072560867091741/125000000000000000)⟩,⟨(1000000000000000000/998066803613037983),0,2,(1935067422872749/1000000000000000000)⟩,(14011059778509779/1000000000000000000)⟩
theorem valid569 : certificate569.Valid := by decide +kernel
theorem sound569 : 0 ≤ cappedLabelEntropy (certificate569.rho:ℝ) ∧ cappedLabelEntropy (certificate569.rho:ℝ) ≤ (certificate569.bound:ℝ) := rat_label_entropy_certificate_sound certificate569 valid569

def certificate570 : RatLabelEntropyCertificate := ⟨(5915466134029527/500000000000000000),⟨(500000000000000000/5915466134029527),6,9,(2218518899340929353/500000000000000000)⟩,⟨(500000000000000000/494084533865970473),0,3,(11901474687654301/1000000000000000000)⟩,(64254962813757559/1000000000000000000)⟩
theorem valid570 : certificate570.Valid := by decide +kernel
theorem sound570 : 0 ≤ cappedLabelEntropy (certificate570.rho:ℝ) ∧ cappedLabelEntropy (certificate570.rho:ℝ) ≤ (certificate570.bound:ℝ) := rat_label_entropy_certificate_sound certificate570 valid570

def certificate571 : RatLabelEntropyCertificate := ⟨(94927197118529643/1000000000000000000),⟨(1000000000000000000/94927197118529643),3,8,(235464502729563303/100000000000000000)⟩,⟨(1000000000000000000/905072802881470357),0,5,(99739893344854909/1000000000000000000)⟩,(313791717478984913/1000000000000000000)⟩
theorem valid571 : certificate571.Valid := by decide +kernel
theorem sound571 : 0 ≤ cappedLabelEntropy (certificate571.rho:ℝ) ∧ cappedLabelEntropy (certificate571.rho:ℝ) ≤ (certificate571.bound:ℝ) := rat_label_entropy_certificate_sound certificate571 valid571

def certificate572 : RatLabelEntropyCertificate := ⟨(2145204999554671/1000000000000000000),⟨(1000000000000000000/2145204999554671),8,14,(6144520160280804609/1000000000000000000)⟩,⟨(1000000000000000000/997854795000445329),0,2,(429501849555877/200000000000000000)⟩,(1532415776790331/100000000000000000)⟩
theorem valid572 : certificate572.Valid := by decide +kernel
theorem sound572 : 0 ≤ cappedLabelEntropy (certificate572.rho:ℝ) ∧ cappedLabelEntropy (certificate572.rho:ℝ) ≤ (certificate572.bound:ℝ) := rat_label_entropy_certificate_sound certificate572 valid572

def certificate573 : RatLabelEntropyCertificate := ⟨(859767687253953/500000000000000000),⟨(500000000000000000/859767687253953),9,6,(6365701155748807531/1000000000000000000)⟩,⟨(500000000000000000/499140232312746047),0,2,(344203094484767/200000000000000000)⟩,(12664104446294863/1000000000000000000)⟩
theorem valid573 : certificate573.Valid := by decide +kernel
theorem sound573 : 0 ≤ cappedLabelEntropy (certificate573.rho:ℝ) ∧ cappedLabelEntropy (certificate573.rho:ℝ) ≤ (certificate573.bound:ℝ) := rat_label_entropy_certificate_sound certificate573 valid573

def certificate574 : RatLabelEntropyCertificate := ⟨(1982831015913249/1000000000000000000),⟨(1000000000000000000/1982831015913249),8,15,(6223229649458228187/1000000000000000000)⟩,⟨(1000000000000000000/998017168984086751),0,2,(1984799427781221/1000000000000000000)⟩,(14320476674012161/1000000000000000000)⟩
theorem valid574 : certificate574.Valid := by decide +kernel
theorem sound574 : 0 ≤ cappedLabelEntropy (certificate574.rho:ℝ) ∧ cappedLabelEntropy (certificate574.rho:ℝ) ≤ (certificate574.bound:ℝ) := rat_label_entropy_certificate_sound certificate574 valid574

def certificate575 : RatLabelEntropyCertificate := ⟨(5836093905239181/500000000000000000),⟨(500000000000000000/5836093905239181),6,9,(2225273188602922797/500000000000000000)⟩,⟨(500000000000000000/494163906094760819),0,3,(733802659471281/62500000000000000)⟩,(12710282881243273/200000000000000000)⟩
theorem valid575 : certificate575.Valid := by decide +kernel
theorem sound575 : 0 ≤ cappedLabelEntropy (certificate575.rho:ℝ) ∧ cappedLabelEntropy (certificate575.rho:ℝ) ≤ (certificate575.bound:ℝ) := rat_label_entropy_certificate_sound certificate575 valid575

def certificate576 : RatLabelEntropyCertificate := ⟨(94853816228347317/1000000000000000000),⟨(1000000000000000000/94853816228347317),3,8,(1177709174528929943/500000000000000000)⟩,⟨(1000000000000000000/905146183771652683),0,5,(99658819297169449/1000000000000000000)⟩,(313626219188433141/1000000000000000000)⟩
theorem valid576 : certificate576.Valid := by decide +kernel
theorem sound576 : 0 ≤ cappedLabelEntropy (certificate576.rho:ℝ) ∧ cappedLabelEntropy (certificate576.rho:ℝ) ≤ (certificate576.bound:ℝ) := rat_label_entropy_certificate_sound certificate576 valid576

def certificate577 : RatLabelEntropyCertificate := ⟨(2277827458667151/1000000000000000000),⟨(1000000000000000000/2277827458667151),8,13,(3042266579644844577/500000000000000000)⟩,⟨(1000000000000000000/997722172541332849),0,2,(456085130775263/200000000000000000)⟩,(16134747941105311/1000000000000000000)⟩
theorem valid577 : certificate577.Valid := by decide +kernel
theorem sound577 : 0 ≤ cappedLabelEntropy (certificate577.rho:ℝ) ∧ cappedLabelEntropy (certificate577.rho:ℝ) ≤ (certificate577.bound:ℝ) := rat_label_entropy_certificate_sound certificate577 valid577

def certificate578 : RatLabelEntropyCertificate := ⟨(1828522273856021/1000000000000000000),⟨(1000000000000000000/1828522273856021),9,5,(788030892369772623/125000000000000000)⟩,⟨(1000000000000000000/998171477726143979),0,2,(366039212278417/200000000000000000)⟩,(6677152910303217/500000000000000000)⟩
theorem valid578 : certificate578.Valid := by decide +kernel
theorem sound578 : 0 ≤ cappedLabelEntropy (certificate578.rho:ℝ) ∧ cappedLabelEntropy (certificate578.rho:ℝ) ≤ (certificate578.bound:ℝ) := rat_label_entropy_certificate_sound certificate578 valid578

def certificate579 : RatLabelEntropyCertificate := ⟨(519849324987143/250000000000000000),⟨(250000000000000000/519849324987143),8,15,(1543919296724363953/250000000000000000)⟩,⟨(250000000000000000/249480150675012857),0,2,(1040781124113229/500000000000000000)⟩,(233108130017131/15625000000000000)⟩
theorem valid579 : certificate579.Valid := by decide +kernel
theorem sound579 : 0 ≤ cappedLabelEntropy (certificate579.rho:ℝ) ∧ cappedLabelEntropy (certificate579.rho:ℝ) ≤ (certificate579.bound:ℝ) := rat_label_entropy_certificate_sound certificate579 valid579

end Cycle12.CutLabelCertificates.Entropy028
