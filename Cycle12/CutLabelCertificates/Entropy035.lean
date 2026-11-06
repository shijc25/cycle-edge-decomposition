import Cycle12.RationalLabelEntropy
import Cycle12.RationalMinorityBudget

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CutLabelCertificates.Entropy035

def certificate700 : RatLabelEntropyCertificate := ⟨(1801608590831263/200000000000000000),⟨(200000000000000000/1801608590831263),6,13,(4709637439150754633/1000000000000000000)⟩,⟨(200000000000000000/198198391409168737),0,3,(361954427328941/40000000000000000)⟩,(25695982253937809/500000000000000000)⟩
theorem valid700 : certificate700.Valid := by decide +kernel
theorem sound700 : 0 ≤ cappedLabelEntropy (certificate700.rho:ℝ) ∧ cappedLabelEntropy (certificate700.rho:ℝ) ≤ (certificate700.bound:ℝ) := rat_label_entropy_certificate_sound certificate700 valid700

def certificate701 : RatLabelEntropyCertificate := ⟨(90661158289258917/1000000000000000000),⟨(1000000000000000000/90661158289258917),3,9,(2400626257362443789/1000000000000000000)⟩,⟨(1000000000000000000/909338841710741083),0,5,(23759372776363157/250000000000000000)⟩,(152032419596507441/500000000000000000)⟩
theorem valid701 : certificate701.Valid := by decide +kernel
theorem sound701 : 0 ≤ cappedLabelEntropy (certificate701.rho:ℝ) ∧ cappedLabelEntropy (certificate701.rho:ℝ) ≤ (certificate701.bound:ℝ) := rat_label_entropy_certificate_sound certificate701 valid701

def certificate702 : RatLabelEntropyCertificate := ⟨(96360587822403003/1000000000000000000),⟨(1000000000000000000/96360587822403003),3,8,(1169829000490034633/500000000000000000)⟩,⟨(1000000000000000000/903639412177596997),0,5,(101324878498398803/1000000000000000000)⟩,(79252993480771837/250000000000000000)⟩
theorem valid702 : certificate702.Valid := by decide +kernel
theorem sound702 : 0 ≤ cappedLabelEntropy (certificate702.rho:ℝ) ∧ cappedLabelEntropy (certificate702.rho:ℝ) ≤ (certificate702.bound:ℝ) := rat_label_entropy_certificate_sound certificate702 valid702

def certificate703 : RatLabelEntropyCertificate := ⟨(3961438587287347/1000000000000000000),⟨(1000000000000000000/3961438587287347),7,17,(5531148040067794819/1000000000000000000)⟩,⟨(1000000000000000000/996038561412712653),0,2,(396930586917061/100000000000000000)⟩,(1034595399426363/40000000000000000)⟩
theorem valid703 : certificate703.Valid := by decide +kernel
theorem sound703 : 0 ≤ cappedLabelEntropy (certificate703.rho:ℝ) ∧ cappedLabelEntropy (certificate703.rho:ℝ) ≤ (certificate703.bound:ℝ) := rat_label_entropy_certificate_sound certificate703 valid703

def certificate704 : RatLabelEntropyCertificate := ⟨(200628265137453/62500000000000000),⟨(62500000000000000/200628265137453),8,7,(5741468067144219971/1000000000000000000)⟩,⟨(62500000000000000/62299371734862547),0,2,(321521551243709/100000000000000000)⟩,(5408826736280981/250000000000000000)⟩
theorem valid704 : certificate704.Valid := by decide +kernel
theorem sound704 : 0 ≤ cappedLabelEntropy (certificate704.rho:ℝ) ∧ cappedLabelEntropy (certificate704.rho:ℝ) ≤ (certificate704.bound:ℝ) := rat_label_entropy_certificate_sound certificate704 valid704

def certificate705 : RatLabelEntropyCertificate := ⟨(3507733843919487/1000000000000000000),⟨(1000000000000000000/3507733843919487),8,6,(2826392539262584111/500000000000000000)⟩,⟨(1000000000000000000/996492266156080513),0,2,(878475091712491/250000000000000000)⟩,(23330040071954811/1000000000000000000)⟩
theorem valid705 : certificate705.Valid := by decide +kernel
theorem sound705 : 0 ≤ cappedLabelEntropy (certificate705.rho:ℝ) ∧ cappedLabelEntropy (certificate705.rho:ℝ) ≤ (certificate705.bound:ℝ) := rat_label_entropy_certificate_sound certificate705 valid705

def certificate706 : RatLabelEntropyCertificate := ⟨(923664831433427/100000000000000000),⟨(100000000000000000/923664831433427),6,12,(4684576195677268267/1000000000000000000)⟩,⟨(100000000000000000/99076335168566573),0,3,(1159946332571263/125000000000000000)⟩,(52463641351043291/1000000000000000000)⟩
theorem valid706 : certificate706.Valid := by decide +kernel
theorem sound706 : 0 ≤ cappedLabelEntropy (certificate706.rho:ℝ) ∧ cappedLabelEntropy (certificate706.rho:ℝ) ≤ (certificate706.bound:ℝ) := rat_label_entropy_certificate_sound certificate706 valid706

def certificate707 : RatLabelEntropyCertificate := ⟨(90733849196108213/1000000000000000000),⟨(1000000000000000000/90733849196108213),3,10,(479964958393317383/200000000000000000)⟩,⟨(1000000000000000000/909266150803891787),0,5,(95117432496999669/1000000000000000000)⟩,(304232402492273961/1000000000000000000)⟩
theorem valid707 : certificate707.Valid := by decide +kernel
theorem sound707 : 0 ≤ cappedLabelEntropy (certificate707.rho:ℝ) ∧ cappedLabelEntropy (certificate707.rho:ℝ) ≤ (certificate707.bound:ℝ) := rat_label_entropy_certificate_sound certificate707 valid707

def certificate708 : RatLabelEntropyCertificate := ⟨(48161989902531249/500000000000000000),⟨(500000000000000000/48161989902531249),3,8,(585009494925265269/250000000000000000)⟩,⟨(500000000000000000/451838010097468751),0,5,(101284367565232637/1000000000000000000)⟩,(316930025289114897/1000000000000000000)⟩
theorem valid708 : certificate708.Valid := by decide +kernel
theorem sound708 : 0 ≤ cappedLabelEntropy (certificate708.rho:ℝ) ∧ cappedLabelEntropy (certificate708.rho:ℝ) ≤ (certificate708.bound:ℝ) := rat_label_entropy_certificate_sound certificate708 valid708

def certificate709 : RatLabelEntropyCertificate := ⟨(4118442030469111/1000000000000000000),⟨(1000000000000000000/4118442030469111),7,15,(5492280335081056133/1000000000000000000)⟩,⟨(1000000000000000000/995881557969530889),0,2,(412694617008347/100000000000000000)⟩,(26729587756635909/1000000000000000000)⟩
theorem valid709 : certificate709.Valid := by decide +kernel
theorem sound709 : 0 ≤ cappedLabelEntropy (certificate709.rho:ℝ) ∧ cappedLabelEntropy (certificate709.rho:ℝ) ≤ (certificate709.bound:ℝ) := rat_label_entropy_certificate_sound certificate709 valid709

def certificate710 : RatLabelEntropyCertificate := ⟨(3357284471181463/1000000000000000000),⟨(1000000000000000000/3357284471181463),8,6,(1139324564974378833/200000000000000000)⟩,⟨(1000000000000000000/996642715528818537),0,2,(672586559251529/200000000000000000)⟩,(2809603227790429/125000000000000000)⟩
theorem valid710 : certificate710.Valid := by decide +kernel
theorem sound710 : 0 ≤ cappedLabelEntropy (certificate710.rho:ℝ) ∧ cappedLabelEntropy (certificate710.rho:ℝ) ≤ (certificate710.bound:ℝ) := rat_label_entropy_certificate_sound certificate710 valid710

def certificate711 : RatLabelEntropyCertificate := ⟨(3653852152953313/1000000000000000000),⟨(1000000000000000000/3653852152953313),8,5,(28059866417717597/5000000000000000)⟩,⟨(1000000000000000000/996346147847046687),0,2,(228783985989863/62500000000000000)⟩,(4830497870894689/200000000000000000)⟩
theorem valid711 : certificate711.Valid := by decide +kernel
theorem sound711 : 0 ≤ cappedLabelEntropy (certificate711.rho:ℝ) ∧ cappedLabelEntropy (certificate711.rho:ℝ) ≤ (certificate711.bound:ℝ) := rat_label_entropy_certificate_sound certificate711 valid711

def certificate712 : RatLabelEntropyCertificate := ⟨(2330281334075739/250000000000000000),⟨(250000000000000000/2330281334075739),6,12,(4675471913335121481/1000000000000000000)⟩,⟨(250000000000000000/247669718665924261),0,3,(4682419438358701/500000000000000000)⟩,(3303637984397131/62500000000000000)⟩
theorem valid712 : certificate712.Valid := by decide +kernel
theorem sound712 : 0 ≤ cappedLabelEntropy (certificate712.rho:ℝ) ∧ cappedLabelEntropy (certificate712.rho:ℝ) ≤ (certificate712.bound:ℝ) := rat_label_entropy_certificate_sound certificate712 valid712

def certificate713 : RatLabelEntropyCertificate := ⟨(5623377658991329/62500000000000000),⟨(62500000000000000/5623377658991329),3,9,(481646813286227289/200000000000000000)⟩,⟨(62500000000000000/56876622341008671),0,5,(47141077600493329/500000000000000000)⟩,(151238881453228619/500000000000000000)⟩
theorem valid713 : certificate713.Valid := by decide +kernel
theorem sound713 : 0 ≤ cappedLabelEntropy (certificate713.rho:ℝ) ∧ cappedLabelEntropy (certificate713.rho:ℝ) ≤ (certificate713.bound:ℝ) := rat_label_entropy_certificate_sound certificate713 valid713

def certificate714 : RatLabelEntropyCertificate := ⟨(48091533091304809/500000000000000000),⟨(500000000000000000/48091533091304809),3,8,(29268774550161047/12500000000000000)⟩,⟨(500000000000000000/451908466908695191),0,6,(20225689187281813/200000000000000000)⟩,(9894201259353893/31250000000000000)⟩
theorem valid714 : certificate714.Valid := by decide +kernel
theorem sound714 : 0 ≤ cappedLabelEntropy (certificate714.rho:ℝ) ∧ cappedLabelEntropy (certificate714.rho:ℝ) ≤ (certificate714.bound:ℝ) := rat_label_entropy_certificate_sound certificate714 valid714

def certificate715 : RatLabelEntropyCertificate := ⟨(2155120188004941/500000000000000000),⟨(500000000000000000/2155120188004941),7,14,(2723380802362817771/500000000000000000)⟩,⟨(500000000000000000/497844879811995059),0,2,(4319556240774267/1000000000000000000)⟩,(868055928195239/31250000000000000)⟩
theorem valid715 : certificate715.Valid := by decide +kernel
theorem sound715 : 0 ≤ cappedLabelEntropy (certificate715.rho:ℝ) ∧ cappedLabelEntropy (certificate715.rho:ℝ) ≤ (certificate715.bound:ℝ) := rat_label_entropy_certificate_sound certificate715 valid715

def certificate716 : RatLabelEntropyCertificate := ⟨(1754258857946999/500000000000000000),⟨(500000000000000000/1754258857946999),8,6,(2826280816931779707/500000000000000000)⟩,⟨(500000000000000000/498245741142053001),0,2,(3514686998426989/1000000000000000000)⟩,(23334468289420207/1000000000000000000)⟩
theorem valid716 : certificate716.Valid := by decide +kernel
theorem sound716 : 0 ≤ cappedLabelEntropy (certificate716.rho:ℝ) ∧ cappedLabelEntropy (certificate716.rho:ℝ) ≤ (certificate716.bound:ℝ) := rat_label_entropy_certificate_sound certificate716 valid716

def certificate717 : RatLabelEntropyCertificate := ⟨(477512994025131/125000000000000000),⟨(125000000000000000/477512994025131),8,3,(278373882205791721/50000000000000000)⟩,⟨(125000000000000000/124522487005974869),0,2,(1913709592606851/500000000000000000)⟩,(3135142674766927/125000000000000000)⟩
theorem valid717 : certificate717.Valid := by decide +kernel
theorem sound717 : 0 ≤ cappedLabelEntropy (certificate717.rho:ℝ) ∧ cappedLabelEntropy (certificate717.rho:ℝ) ≤ (certificate717.bound:ℝ) := rat_label_entropy_certificate_sound certificate717 valid717

def certificate718 : RatLabelEntropyCertificate := ⟨(2405757521172399/250000000000000000),⟨(250000000000000000/2405757521172399),6,12,(464359608628109693/100000000000000000)⟩,⟨(250000000000000000/247594242478827601),0,3,(483481531934811/50000000000000000)⟩,(54262044331582071/1000000000000000000)⟩
theorem valid718 : certificate718.Valid := by decide +kernel
theorem sound718 : 0 ≤ cappedLabelEntropy (certificate718.rho:ℝ) ∧ cappedLabelEntropy (certificate718.rho:ℝ) ≤ (certificate718.bound:ℝ) := rat_label_entropy_certificate_sound certificate718 valid718

def certificate719 : RatLabelEntropyCertificate := ⟨(5681595541655199/62500000000000000),⟨(62500000000000000/5681595541655199),3,9,(1198967229117397353/500000000000000000)⟩,⟨(62500000000000000/56818404458344801),0,5,(47653130672566767/500000000000000000)⟩,(304627894905739113/1000000000000000000)⟩
theorem valid719 : certificate719.Valid := by decide +kernel
theorem sound719 : 0 ≤ cappedLabelEntropy (certificate719.rho:ℝ) ∧ cappedLabelEntropy (certificate719.rho:ℝ) ≤ (certificate719.bound:ℝ) := rat_label_entropy_certificate_sound certificate719 valid719

end Cycle12.CutLabelCertificates.Entropy035
