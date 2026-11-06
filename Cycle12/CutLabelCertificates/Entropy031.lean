import Cycle12.RationalLabelEntropy
import Cycle12.RationalMinorityBudget

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CutLabelCertificates.Entropy031

def certificate620 : RatLabelEntropyCertificate := ⟨(8950595836773623/1000000000000000000),⟨(1000000000000000000/8950595836773623),6,13,(1179008793742533149/250000000000000000)⟩,⟨(1000000000000000000/991049404163226377),0,3,(1123861631998147/125000000000000000)⟩,(6390218001149379/125000000000000000)⟩
theorem valid620 : certificate620.Valid := by decide +kernel
theorem sound620 : 0 ≤ cappedLabelEntropy (certificate620.rho:ℝ) ∧ cappedLabelEntropy (certificate620.rho:ℝ) ≤ (certificate620.bound:ℝ) := rat_label_entropy_certificate_sound certificate620 valid620

def certificate621 : RatLabelEntropyCertificate := ⟨(96425655854875347/1000000000000000000),⟨(1000000000000000000/96425655854875347),3,8,(467796594640219069/200000000000000000)⟩,⟨(1000000000000000000/903574344145124653),0,6,(101396887725058143/1000000000000000000)⟩,(317157593548828199/1000000000000000000)⟩
theorem valid621 : certificate621.Valid := by decide +kernel
theorem sound621 : 0 ≤ cappedLabelEntropy (certificate621.rho:ℝ) ∧ cappedLabelEntropy (certificate621.rho:ℝ) ≤ (certificate621.bound:ℝ) := rat_label_entropy_certificate_sound certificate621 valid621

def certificate622 : RatLabelEntropyCertificate := ⟨(167477304052983/62500000000000000),⟨(62500000000000000/167477304052983),8,10,(1184414798366245447/200000000000000000)⟩,⟨(62500000000000000/62332522695947017),0,2,(2683233518298381/1000000000000000000)⟩,(18545051211712653/1000000000000000000)⟩
theorem valid622 : certificate622.Valid := by decide +kernel
theorem sound622 : 0 ≤ cappedLabelEntropy (certificate622.rho:ℝ) ∧ cappedLabelEntropy (certificate622.rho:ℝ) ≤ (certificate622.bound:ℝ) := rat_label_entropy_certificate_sound certificate622 valid622

def certificate623 : RatLabelEntropyCertificate := ⟨(2160275520852283/1000000000000000000),⟨(1000000000000000000/2160275520852283),8,14,(767189938683812609/125000000000000000)⟩,⟨(1000000000000000000/997839724479147717),0,2,(1081306140993537/500000000000000000)⟩,(7708336799337819/500000000000000000)⟩
theorem valid623 : certificate623.Valid := by decide +kernel
theorem sound623 : 0 ≤ cappedLabelEntropy (certificate623.rho:ℝ) ∧ cappedLabelEntropy (certificate623.rho:ℝ) ≤ (certificate623.bound:ℝ) := rat_label_entropy_certificate_sound certificate623 valid623

def certificate624 : RatLabelEntropyCertificate := ⟨(1202954902597431/500000000000000000),⟨(500000000000000000/1202954902597431),8,12,(376864196848906499/62500000000000000)⟩,⟨(500000000000000000/498797045097402569),0,2,(150550541044197/62500000000000000)⟩,(27056373669043/1600000000000000)⟩
theorem valid624 : certificate624.Valid := by decide +kernel
theorem sound624 : 0 ≤ cappedLabelEntropy (certificate624.rho:ℝ) ∧ cappedLabelEntropy (certificate624.rho:ℝ) ≤ (certificate624.bound:ℝ) := rat_label_entropy_certificate_sound certificate624 valid624

def certificate625 : RatLabelEntropyCertificate := ⟨(8829240088480081/1000000000000000000),⟨(1000000000000000000/8829240088480081),6,13,(2364843164132220381/500000000000000000)⟩,⟨(1000000000000000000/991170759911519919),0,3,(1773689757608603/200000000000000000)⟩,(25274841629964777/500000000000000000)⟩
theorem valid625 : certificate625.Valid := by decide +kernel
theorem sound625 : 0 ≤ cappedLabelEntropy (certificate625.rho:ℝ) ∧ cappedLabelEntropy (certificate625.rho:ℝ) ≤ (certificate625.bound:ℝ) := rat_label_entropy_certificate_sound certificate625 valid625

def certificate626 : RatLabelEntropyCertificate := ⟨(19268640776941061/200000000000000000),⟨(200000000000000000/19268640776941061),3,8,(2339838422315745697/1000000000000000000)⟩,⟨(200000000000000000/180731359223058939),0,5,(101305640990326283/1000000000000000000)⟩,(158486530572078801/500000000000000000)⟩
theorem valid626 : certificate626.Valid := by decide +kernel
theorem sound626 : 0 ≤ cappedLabelEntropy (certificate626.rho:ℝ) ∧ cappedLabelEntropy (certificate626.rho:ℝ) ≤ (certificate626.bound:ℝ) := rat_label_entropy_certificate_sound certificate626 valid626

def certificate627 : RatLabelEntropyCertificate := ⟨(2715944451293659/1000000000000000000),⟨(1000000000000000000/2715944451293659),8,10,(5908615521890400467/1000000000000000000)⟩,⟨(1000000000000000000/997284055548706341),0,2,(2719639319979999/1000000000000000000)⟩,(46899311180413/2500000000000000)⟩
theorem valid627 : certificate627.Valid := by decide +kernel
theorem sound627 : 0 ≤ cappedLabelEntropy (certificate627.rho:ℝ) ∧ cappedLabelEntropy (certificate627.rho:ℝ) ≤ (certificate627.bound:ℝ) := rat_label_entropy_certificate_sound certificate627 valid627

def certificate628 : RatLabelEntropyCertificate := ⟨(1093957880221963/500000000000000000),⟨(500000000000000000/1093957880221963),8,14,(3062402947937379621/500000000000000000)⟩,⟨(500000000000000000/498906042119778037),0,2,(547578186259111/250000000000000000)⟩,(15586079874505543/1000000000000000000)⟩
theorem valid628 : certificate628.Valid := by decide +kernel
theorem sound628 : 0 ≤ cappedLabelEntropy (certificate628.rho:ℝ) ∧ cappedLabelEntropy (certificate628.rho:ℝ) ≤ (certificate628.bound:ℝ) := rat_label_entropy_certificate_sound certificate628 valid628

def certificate629 : RatLabelEntropyCertificate := ⟨(2448303572916619/1000000000000000000),⟨(1000000000000000000/2448303572916619),8,12,(3006179956738055411/500000000000000000)⟩,⟨(1000000000000000000/997551696427083381),0,2,(2451305568975319/1000000000000000000)⟩,(17165386286616703/1000000000000000000)⟩
theorem valid629 : certificate629.Valid := by decide +kernel
theorem sound629 : 0 ≤ cappedLabelEntropy (certificate629.rho:ℝ) ∧ cappedLabelEntropy (certificate629.rho:ℝ) ≤ (certificate629.bound:ℝ) := rat_label_entropy_certificate_sound certificate629 valid629

def certificate630 : RatLabelEntropyCertificate := ⟨(4634815573951209/500000000000000000),⟨(500000000000000000/4634815573951209),6,12,(1170252922516575119/250000000000000000)⟩,⟨(500000000000000000/495365184426048791),0,3,(9312861539293901/1000000000000000000)⟩,(52617786513827079/1000000000000000000)⟩
theorem valid630 : certificate630.Valid := by decide +kernel
theorem sound630 : 0 ≤ cappedLabelEntropy (certificate630.rho:ℝ) ∧ cappedLabelEntropy (certificate630.rho:ℝ) ≤ (certificate630.bound:ℝ) := rat_label_entropy_certificate_sound certificate630 valid630

def certificate631 : RatLabelEntropyCertificate := ⟨(2406358454864909/25000000000000000),⟨(25000000000000000/2406358454864909),3,8,(2340761234678311861/1000000000000000000)⟩,⟨(25000000000000000/22593641545135091),0,6,(101207305736004687/1000000000000000000)⟩,(316774087017454547/1000000000000000000)⟩
theorem valid631 : certificate631.Valid := by decide +kernel
theorem sound631 : 0 ≤ cappedLabelEntropy (certificate631.rho:ℝ) ∧ cappedLabelEntropy (certificate631.rho:ℝ) ≤ (certificate631.bound:ℝ) := rat_label_entropy_certificate_sound certificate631 valid631

def certificate632 : RatLabelEntropyCertificate := ⟨(1366323323983619/500000000000000000),⟨(500000000000000000/1366323323983619),8,10,(2951242335648057757/500000000000000000)⟩,⟨(500000000000000000/498633676676016381),0,2,(684096785668199/250000000000000000)⟩,(9429157257607583/500000000000000000)⟩
theorem valid632 : certificate632.Valid := by decide +kernel
theorem sound632 : 0 ≤ cappedLabelEntropy (certificate632.rho:ℝ) ∧ cappedLabelEntropy (certificate632.rho:ℝ) ≤ (certificate632.bound:ℝ) := rat_label_entropy_certificate_sound certificate632 valid632

def certificate633 : RatLabelEntropyCertificate := ⟨(2217029452788511/1000000000000000000),⟨(1000000000000000000/2217029452788511),8,14,(6111587063461687059/1000000000000000000)⟩,⟨(1000000000000000000/997782970547211489),0,2,(554872675257973/250000000000000000)⟩,(15764138547753321/1000000000000000000)⟩
theorem valid633 : certificate633.Valid := by decide +kernel
theorem sound633 : 0 ≤ cappedLabelEntropy (certificate633.rho:ℝ) ∧ cappedLabelEntropy (certificate633.rho:ℝ) ≤ (certificate633.bound:ℝ) := rat_label_entropy_certificate_sound certificate633 valid633

def certificate634 : RatLabelEntropyCertificate := ⟨(2470128949337487/1000000000000000000),⟨(1000000000000000000/2470128949337487),8,12,(3001742461747719523/500000000000000000)⟩,⟨(1000000000000000000/997529871050662513),0,2,(494636950207473/200000000000000000)⟩,(135128574783/7812500000000)⟩
theorem valid634 : certificate634.Valid := by decide +kernel
theorem sound634 : 0 ≤ cappedLabelEntropy (certificate634.rho:ℝ) ∧ cappedLabelEntropy (certificate634.rho:ℝ) ≤ (certificate634.bound:ℝ) := rat_label_entropy_certificate_sound certificate634 valid634

def certificate635 : RatLabelEntropyCertificate := ⟨(9088674341803591/1000000000000000000),⟨(1000000000000000000/9088674341803591),6,13,(4700726218413300269/1000000000000000000)⟩,⟨(1000000000000000000/990911325658196409),0,3,(2282557078606183/250000000000000000)⟩,(51770616411744997/1000000000000000000)⟩
theorem valid635 : certificate635.Valid := by decide +kernel
theorem sound635 : 0 ≤ cappedLabelEntropy (certificate635.rho:ℝ) ∧ cappedLabelEntropy (certificate635.rho:ℝ) ≤ (certificate635.bound:ℝ) := rat_label_entropy_certificate_sound certificate635 valid635

def certificate636 : RatLabelEntropyCertificate := ⟨(12026947674975669/125000000000000000),⟨(125000000000000000/12026947674975669),3,8,(1170581982806531399/500000000000000000)⟩,⟨(125000000000000000/112973052325024331),0,5,(25291105507357381/250000000000000000)⟩,(79171820112656857/250000000000000000)⟩
theorem valid636 : certificate636.Valid := by decide +kernel
theorem sound636 : 0 ≤ cappedLabelEntropy (certificate636.rho:ℝ) ∧ cappedLabelEntropy (certificate636.rho:ℝ) ≤ (certificate636.bound:ℝ) := rat_label_entropy_certificate_sound certificate636 valid636

def certificate637 : RatLabelEntropyCertificate := ⟨(2769735994194639/1000000000000000000),⟨(1000000000000000000/2769735994194639),8,9,(2944501636140040477/500000000000000000)⟩,⟨(1000000000000000000/997230264005805361),0,2,(1386789405148829/500000000000000000)⟩,(9538440531199097/500000000000000000)⟩
theorem valid637 : certificate637.Valid := by decide +kernel
theorem sound637 : 0 ≤ cappedLabelEntropy (certificate637.rho:ℝ) ∧ cappedLabelEntropy (certificate637.rho:ℝ) ≤ (certificate637.bound:ℝ) := rat_label_entropy_certificate_sound certificate637 valid637

def certificate638 : RatLabelEntropyCertificate := ⟨(224598755874639/100000000000000000),⟨(100000000000000000/224598755874639),8,13,(304930498098745483/50000000000000000)⟩,⟨(100000000000000000/99775401244125361),0,2,(281064196471841/125000000000000000)⟩,(3985216384627323/250000000000000000)⟩
theorem valid638 : certificate638.Valid := by decide +kernel
theorem sound638 : 0 ≤ cappedLabelEntropy (certificate638.rho:ℝ) ∧ cappedLabelEntropy (certificate638.rho:ℝ) ≤ (certificate638.bound:ℝ) := rat_label_entropy_certificate_sound certificate638 valid638

def certificate639 : RatLabelEntropyCertificate := ⟨(2502776589723271/1000000000000000000),⟨(1000000000000000000/2502776589723271),8,11,(299517726375921601/50000000000000000)⟩,⟨(1000000000000000000/997497223410276729),0,2,(2505913770587367/1000000000000000000)⟩,(8746080551941207/500000000000000000)⟩
theorem valid639 : certificate639.Valid := by decide +kernel
theorem sound639 : 0 ≤ cappedLabelEntropy (certificate639.rho:ℝ) ∧ cappedLabelEntropy (certificate639.rho:ℝ) ≤ (certificate639.bound:ℝ) := rat_label_entropy_certificate_sound certificate639 valid639

end Cycle12.CutLabelCertificates.Entropy031
