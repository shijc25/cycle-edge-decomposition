import Cycle12.RationalLabelEntropy
import Cycle12.RationalMinorityBudget

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CutLabelCertificates.Entropy032

def certificate640 : RatLabelEntropyCertificate := ⟨(182803285799777/20000000000000000),⟨(20000000000000000/182803285799777),6,13,(939015383768591503/200000000000000000)⟩,⟨(20000000000000000/19817196714200223),0,3,(367287675214023/40000000000000000)⟩,(812688117662207/15625000000000000)⟩
theorem valid640 : certificate640.Valid := by decide +kernel
theorem sound640 : 0 ≤ cappedLabelEntropy (certificate640.rho:ℝ) ∧ cappedLabelEntropy (certificate640.rho:ℝ) ≤ (certificate640.bound:ℝ) := rat_label_entropy_certificate_sound certificate640 valid640

def certificate641 : RatLabelEntropyCertificate := ⟨(19236477483661101/200000000000000000),⟨(200000000000000000/19236477483661101),3,8,(2341509021042006297/1000000000000000000)⟩,⟨(200000000000000000/180763522516338899),0,5,(25281923734784943/250000000000000000)⟩,(79153229902775681/250000000000000000)⟩
theorem valid641 : certificate641.Valid := by decide +kernel
theorem sound641 : 0 ≤ cappedLabelEntropy (certificate641.rho:ℝ) ∧ cappedLabelEntropy (certificate641.rho:ℝ) ≤ (certificate641.bound:ℝ) := rat_label_entropy_certificate_sound certificate641 valid641

def certificate642 : RatLabelEntropyCertificate := ⟨(1394077191111319/500000000000000000),⟨(500000000000000000/1394077191111319),8,9,(367648463362028601/62500000000000000)⟩,⟨(500000000000000000/498605922808888681),0,2,(349006065581251/125000000000000000)⟩,(4796308662541193/250000000000000000)⟩
theorem valid642 : certificate642.Valid := by decide +kernel
theorem sound642 : 0 ≤ cappedLabelEntropy (certificate642.rho:ℝ) ∧ cappedLabelEntropy (certificate642.rho:ℝ) ≤ (certificate642.bound:ℝ) := rat_label_entropy_certificate_sound certificate642 valid642

def certificate643 : RatLabelEntropyCertificate := ⟨(1130175493322527/500000000000000000),⟨(500000000000000000/1130175493322527),8,13,(3046117586965544009/500000000000000000)⟩,⟨(500000000000000000/498869824506677473),0,2,(2262909435992549/1000000000000000000)⟩,(4007096063171263/250000000000000000)⟩
theorem valid643 : certificate643.Valid := by decide +kernel
theorem sound643 : 0 ≤ cappedLabelEntropy (certificate643.rho:ℝ) ∧ cappedLabelEntropy (certificate643.rho:ℝ) ≤ (certificate643.bound:ℝ) := rat_label_entropy_certificate_sound certificate643 valid643

def certificate644 : RatLabelEntropyCertificate := ⟨(314886041060057/125000000000000000),⟨(125000000000000000/314886041060057),8,11,(5983858217327472733/1000000000000000000)⟩,⟨(125000000000000000/124685113958939943),0,2,(126113328506003/50000000000000000)⟩,(17589780152393459/1000000000000000000)⟩
theorem valid644 : certificate644.Valid := by decide +kernel
theorem sound644 : 0 ≤ cappedLabelEntropy (certificate644.rho:ℝ) ∧ cappedLabelEntropy (certificate644.rho:ℝ) ≤ (certificate644.bound:ℝ) := rat_label_entropy_certificate_sound certificate644 valid644

def certificate645 : RatLabelEntropyCertificate := ⟨(4603417622862239/500000000000000000),⟨(500000000000000000/4603417622862239),6,13,(1171952277323653433/250000000000000000)⟩,⟨(500000000000000000/495396582377137761),0,3,(9249480104621083/1000000000000000000)⟩,(3270262987366947/62500000000000000)⟩
theorem valid645 : certificate645.Valid := by decide +kernel
theorem sound645 : 0 ≤ cappedLabelEntropy (certificate645.rho:ℝ) ∧ cappedLabelEntropy (certificate645.rho:ℝ) ≤ (certificate645.bound:ℝ) := rat_label_entropy_certificate_sound certificate645 valid645

def certificate646 : RatLabelEntropyCertificate := ⟨(48065698498318913/500000000000000000),⟨(500000000000000000/48065698498318913),3,8,(292754913080118149/125000000000000000)⟩,⟨(500000000000000000/451934301501681087),0,6,(50535639907194521/500000000000000000)⟩,(316498666665762043/1000000000000000000)⟩
theorem valid646 : certificate646.Valid := by decide +kernel
theorem sound646 : 0 ≤ cappedLabelEntropy (certificate646.rho:ℝ) ∧ cappedLabelEntropy (certificate646.rho:ℝ) ≤ (certificate646.bound:ℝ) := rat_label_entropy_certificate_sound certificate646 valid646

def certificate647 : RatLabelEntropyCertificate := ⟨(2806939333681323/1000000000000000000),⟨(1000000000000000000/2806939333681323),8,9,(5875660594347052173/1000000000000000000)⟩,⟨(1000000000000000000/997193060666318677),0,2,(2810886175319691/1000000000000000000)⟩,(19295619021985807/1000000000000000000)⟩
theorem valid647 : certificate647.Valid := by decide +kernel
theorem sound647 : 0 ≤ cappedLabelEntropy (certificate647.rho:ℝ) ∧ cappedLabelEntropy (certificate647.rho:ℝ) ≤ (certificate647.bound:ℝ) := rat_label_entropy_certificate_sound certificate647 valid647

def certificate648 : RatLabelEntropyCertificate := ⟨(1137568088480833/500000000000000000),⟨(500000000000000000/1137568088480833),8,13,(95089302661961161/15625000000000000)⟩,⟨(500000000000000000/498862431911519167),0,2,(1779475180889/781250000000000)⟩,(16118377291447307/1000000000000000000)⟩
theorem valid648 : certificate648.Valid := by decide +kernel
theorem sound648 : 0 ≤ cappedLabelEntropy (certificate648.rho:ℝ) ∧ cappedLabelEntropy (certificate648.rho:ℝ) ≤ (certificate648.bound:ℝ) := rat_label_entropy_certificate_sound certificate648 valid648

def certificate649 : RatLabelEntropyCertificate := ⟨(2535722979808561/1000000000000000000),⟨(1000000000000000000/2535722979808561),8,11,(597727648346500609/100000000000000000)⟩,⟨(1000000000000000000/997464277020191439),0,2,(2538943370488093/1000000000000000000)⟩,(4422305662307659/250000000000000000)⟩
theorem valid649 : certificate649.Valid := by decide +kernel
theorem sound649 : 0 ≤ cappedLabelEntropy (certificate649.rho:ℝ) ∧ cappedLabelEntropy (certificate649.rho:ℝ) ≤ (certificate649.bound:ℝ) := rat_label_entropy_certificate_sound certificate649 valid649

def certificate650 : RatLabelEntropyCertificate := ⟨(9271274079821197/1000000000000000000),⟨(1000000000000000000/9271274079821197),6,14,(936166893531927599/200000000000000000)⟩,⟨(1000000000000000000/990728725920178803),0,3,(9314519844452069/1000000000000000000)⟩,(26312730824999337/500000000000000000)⟩
theorem valid650 : certificate650.Valid := by decide +kernel
theorem sound650 : 0 ≤ cappedLabelEntropy (certificate650.rho:ℝ) ∧ cappedLabelEntropy (certificate650.rho:ℝ) ≤ (certificate650.bound:ℝ) := rat_label_entropy_certificate_sound certificate650 valid650

def certificate651 : RatLabelEntropyCertificate := ⟨(96106564551510011/1000000000000000000),⟨(1000000000000000000/96106564551510011),3,9,(468459531149961997/200000000000000000)⟩,⟨(1000000000000000000/903893435448489989),0,5,(101043806679539233/1000000000000000000)⟩,(63288602880306297/200000000000000000)⟩
theorem valid651 : certificate651.Valid := by decide +kernel
theorem sound651 : 0 ≤ cappedLabelEntropy (certificate651.rho:ℝ) ∧ cappedLabelEntropy (certificate651.rho:ℝ) ≤ (certificate651.bound:ℝ) := rat_label_entropy_certificate_sound certificate651 valid651

def certificate652 : RatLabelEntropyCertificate := ⟨(37426019682253/12500000000000000),⟨(12500000000000000/37426019682253),8,9,(5811117747337082231/1000000000000000000)⟩,⟨(12500000000000000/12462573980317747),0,2,(749643200948991/250000000000000000)⟩,(2038855540723227/100000000000000000)⟩
theorem valid652 : certificate652.Valid := by decide +kernel
theorem sound652 : 0 ≤ cappedLabelEntropy (certificate652.rho:ℝ) ∧ cappedLabelEntropy (certificate652.rho:ℝ) ≤ (certificate652.bound:ℝ) := rat_label_entropy_certificate_sound certificate652 valid652

def certificate653 : RatLabelEntropyCertificate := ⟨(2401292434017869/1000000000000000000),⟨(1000000000000000000/2401292434017869),8,12,(1206349634480169597/200000000000000000)⟩,⟨(1000000000000000000/997598707565982131),0,2,(300522520058927/125000000000000000)⟩,(8441199135564663/500000000000000000)⟩
theorem valid653 : certificate653.Valid := by decide +kernel
theorem sound653 : 0 ≤ cappedLabelEntropy (certificate653.rho:ℝ) ∧ cappedLabelEntropy (certificate653.rho:ℝ) ≤ (certificate653.bound:ℝ) := rat_label_entropy_certificate_sound certificate653 valid653

def certificate654 : RatLabelEntropyCertificate := ⟨(1332256819540659/500000000000000000),⟨(500000000000000000/1332256819540659),8,10,(2963866868713003593/500000000000000000)⟩,⟨(500000000000000000/498667743180459341),0,2,(533613954773091/200000000000000000)⟩,(18455488057777043/1000000000000000000)⟩
theorem valid654 : certificate654.Valid := by decide +kernel
theorem sound654 : 0 ≤ cappedLabelEntropy (certificate654.rho:ℝ) ∧ cappedLabelEntropy (certificate654.rho:ℝ) ≤ (certificate654.bound:ℝ) := rat_label_entropy_certificate_sound certificate654 valid654

def certificate655 : RatLabelEntropyCertificate := ⟨(9152442305026601/1000000000000000000),⟨(1000000000000000000/9152442305026601),6,13,(4693734516728992017/1000000000000000000)⟩,⟨(1000000000000000000/990847557694973399),0,3,(9194583230434617/1000000000000000000)⟩,(26034782348686657/500000000000000000)⟩
theorem valid655 : certificate655.Valid := by decide +kernel
theorem sound655 : 0 ≤ cappedLabelEntropy (certificate655.rho:ℝ) ∧ cappedLabelEntropy (certificate655.rho:ℝ) ≤ (certificate655.bound:ℝ) := rat_label_entropy_certificate_sound certificate655 valid655

def certificate656 : RatLabelEntropyCertificate := ⟨(48072549679574489/500000000000000000),⟨(500000000000000000/48072549679574489),3,8,(1170948388474947799/500000000000000000)⟩,⟨(500000000000000000/451927450320425511),0,5,(101086439613422237/1000000000000000000)⟩,(39566171517705701/125000000000000000)⟩
theorem valid656 : certificate656.Valid := by decide +kernel
theorem sound656 : 0 ≤ cappedLabelEntropy (certificate656.rho:ℝ) ∧ cappedLabelEntropy (certificate656.rho:ℝ) ≤ (certificate656.bound:ℝ) := rat_label_entropy_certificate_sound certificate656 valid656

def certificate657 : RatLabelEntropyCertificate := ⟨(3154072735001799/1000000000000000000),⟨(1000000000000000000/3154072735001799),8,8,(359941295594655517/62500000000000000)⟩,⟨(1000000000000000000/996845927264998201),0,2,(631811461260753/200000000000000000)⟩,(10656794917983431/500000000000000000)⟩
theorem valid657 : certificate657.Valid := by decide +kernel
theorem sound657 : 0 ≤ cappedLabelEntropy (certificate657.rho:ℝ) ∧ cappedLabelEntropy (certificate657.rho:ℝ) ≤ (certificate657.bound:ℝ) := rat_label_entropy_certificate_sound certificate657 valid657

def certificate658 : RatLabelEntropyCertificate := ⟨(2525638994904119/1000000000000000000),⟨(1000000000000000000/2525638994904119),8,11,(5981261180982178849/1000000000000000000)⟩,⟨(1000000000000000000/997474361005095881),0,2,(252883380148951/100000000000000000)⟩,(17628953357623691/1000000000000000000)⟩
theorem valid658 : certificate658.Valid := by decide +kernel
theorem sound658 : 0 ≤ cappedLabelEntropy (certificate658.rho:ℝ) ∧ cappedLabelEntropy (certificate658.rho:ℝ) ≤ (certificate658.bound:ℝ) := rat_label_entropy_certificate_sound certificate658 valid658

def certificate659 : RatLabelEntropyCertificate := ⟨(140197848979219/50000000000000000),⟨(50000000000000000/140197848979219),8,9,(5876723652443760617/1000000000000000000)⟩,⟨(50000000000000000/49859802151020781),0,2,(280789543084417/100000000000000000)⟩,(3855620503042241/200000000000000000)⟩
theorem valid659 : certificate659.Valid := by decide +kernel
theorem sound659 : 0 ≤ cappedLabelEntropy (certificate659.rho:ℝ) ∧ cappedLabelEntropy (certificate659.rho:ℝ) ≤ (certificate659.bound:ℝ) := rat_label_entropy_certificate_sound certificate659 valid659

end Cycle12.CutLabelCertificates.Entropy032
