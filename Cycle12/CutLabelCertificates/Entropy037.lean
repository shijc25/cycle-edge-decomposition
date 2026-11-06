import Cycle12.RationalLabelEntropy
import Cycle12.RationalMinorityBudget

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CutLabelCertificates.Entropy037

def certificate740 : RatLabelEntropyCertificate := ⟨(4154306352176991/1000000000000000000),⟨(1000000000000000000/4154306352176991),7,14,(548360980752893721/100000000000000000)⟩,⟨(1000000000000000000/995845693647823009),0,2,(4162959456222557/1000000000000000000)⟩,(6731565075896807/250000000000000000)⟩
theorem valid740 : certificate740.Valid := by decide +kernel
theorem sound740 : 0 ≤ cappedLabelEntropy (certificate740.rho:ℝ) ∧ cappedLabelEntropy (certificate740.rho:ℝ) ≤ (certificate740.bound:ℝ) := rat_label_entropy_certificate_sound certificate740 valid740

def certificate741 : RatLabelEntropyCertificate := ⟨(2234865189725371/500000000000000000),⟨(500000000000000000/2234865189725371),7,14,(1690758496866283/312500000000000)⟩,⟨(500000000000000000/497765134810274629),0,2,(895949898116091/200000000000000000)⟩,(2864287699501471/100000000000000000)⟩
theorem valid741 : certificate741.Valid := by decide +kernel
theorem sound741 : 0 ≤ cappedLabelEntropy (certificate741.rho:ℝ) ∧ cappedLabelEntropy (certificate741.rho:ℝ) ≤ (certificate741.bound:ℝ) := rat_label_entropy_certificate_sound certificate741 valid741

def certificate742 : RatLabelEntropyCertificate := ⟨(4953014703184773/500000000000000000),⟨(500000000000000000/4953014703184773),6,12,(4614611676279254927/1000000000000000000)⟩,⟨(500000000000000000/495046985296815227),0,3,(4977710283276947/500000000000000000)⟩,(55569280841867399/1000000000000000000)⟩
theorem valid742 : certificate742.Valid := by decide +kernel
theorem sound742 : 0 ≤ cappedLabelEntropy (certificate742.rho:ℝ) ∧ cappedLabelEntropy (certificate742.rho:ℝ) ≤ (certificate742.bound:ℝ) := rat_label_entropy_certificate_sound certificate742 valid742

def certificate743 : RatLabelEntropyCertificate := ⟨(8703647895827039/100000000000000000),⟨(100000000000000000/8703647895827039),3,10,(1220713974918813263/500000000000000000)⟩,⟨(100000000000000000/91296352104172961),0,5,(9105935423278639/100000000000000000)⟩,(147813580524163293/500000000000000000)⟩
theorem valid743 : certificate743.Valid := by decide +kernel
theorem sound743 : 0 ≤ cappedLabelEntropy (certificate743.rho:ℝ) ∧ cappedLabelEntropy (certificate743.rho:ℝ) ≤ (certificate743.bound:ℝ) := rat_label_entropy_certificate_sound certificate743 valid743

def certificate744 : RatLabelEntropyCertificate := ⟨(47762728096862397/500000000000000000),⟨(500000000000000000/47762728096862397),3,8,(2348362510013104447/1000000000000000000)⟩,⟨(500000000000000000/452237271903137603),0,5,(100401118482829583/1000000000000000000)⟩,(63027731182927897/200000000000000000)⟩
theorem valid744 : certificate744.Valid := by decide +kernel
theorem sound744 : 0 ≤ cappedLabelEntropy (certificate744.rho:ℝ) ∧ cappedLabelEntropy (certificate744.rho:ℝ) ≤ (certificate744.bound:ℝ) := rat_label_entropy_certificate_sound certificate744 valid744

def certificate745 : RatLabelEntropyCertificate := ⟨(212724584632999/40000000000000000),⟨(40000000000000000/212724584632999),7,10,(5236636433963139003/1000000000000000000)⟩,⟨(40000000000000000/39787275415367001),0,3,(1333076531108287/250000000000000000)⟩,(16576490533258847/500000000000000000)⟩
theorem valid745 : certificate745.Valid := by decide +kernel
theorem sound745 : 0 ≤ cappedLabelEntropy (certificate745.rho:ℝ) ∧ cappedLabelEntropy (certificate745.rho:ℝ) ≤ (certificate745.bound:ℝ) := rat_label_entropy_certificate_sound certificate745 valid745

def certificate746 : RatLabelEntropyCertificate := ⟨(865256313559061/200000000000000000),⟨(200000000000000000/865256313559061),7,14,(5443046866238035077/1000000000000000000)⟩,⟨(200000000000000000/199134743686440939),0,2,(4335667003035939/1000000000000000000)⟩,(5573012603369643/200000000000000000)⟩
theorem valid746 : certificate746.Valid := by decide +kernel
theorem sound746 : 0 ≤ cappedLabelEntropy (certificate746.rho:ℝ) ∧ cappedLabelEntropy (certificate746.rho:ℝ) ≤ (certificate746.bound:ℝ) := rat_label_entropy_certificate_sound certificate746 valid746

def certificate747 : RatLabelEntropyCertificate := ⟨(7450403374379/1600000000000000),⟨(1600000000000000/7450403374379),7,13,(2684745366545101543/500000000000000000)⟩,⟨(1600000000000000/1592549596625621),0,2,(4667377388573719/1000000000000000000)⟩,(29648688658740401/1000000000000000000)⟩
theorem valid747 : certificate747.Valid := by decide +kernel
theorem sound747 : 0 ≤ cappedLabelEntropy (certificate747.rho:ℝ) ∧ cappedLabelEntropy (certificate747.rho:ℝ) ≤ (certificate747.bound:ℝ) := rat_label_entropy_certificate_sound certificate747 valid747

def certificate748 : RatLabelEntropyCertificate := ⟨(2038773119115099/200000000000000000),⟨(200000000000000000/2038773119115099),6,13,(4585969151811251089/1000000000000000000)⟩,⟨(200000000000000000/197961226880884901),0,3,(10246178863406499/1000000000000000000)⟩,(28445241926111977/500000000000000000)⟩
theorem valid748 : certificate748.Valid := by decide +kernel
theorem sound748 : 0 ≤ cappedLabelEntropy (certificate748.rho:ℝ) ∧ cappedLabelEntropy (certificate748.rho:ℝ) ≤ (certificate748.bound:ℝ) := rat_label_entropy_certificate_sound certificate748 valid748

def certificate749 : RatLabelEntropyCertificate := ⟨(88491857935282613/1000000000000000000),⟨(1000000000000000000/88491857935282613),3,10,(2424844731931849993/1000000000000000000)⟩,⟨(1000000000000000000/911508142064717387),0,5,(926547523035151/10000000000000000)⟩,(299034576658875363/1000000000000000000)⟩
theorem valid749 : certificate749.Valid := by decide +kernel
theorem sound749 : 0 ≤ cappedLabelEntropy (certificate749.rho:ℝ) ∧ cappedLabelEntropy (certificate749.rho:ℝ) ≤ (certificate749.bound:ℝ) := rat_label_entropy_certificate_sound certificate749 valid749

def certificate750 : RatLabelEntropyCertificate := ⟨(95402709968737791/1000000000000000000),⟨(1000000000000000000/95402709968737791),3,8,(2349648294550450531/1000000000000000000)⟩,⟨(1000000000000000000/904597290031262209),0,5,(100265417707570719/1000000000000000000)⟩,(15743131995782851/50000000000000000)⟩
theorem valid750 : certificate750.Valid := by decide +kernel
theorem sound750 : 0 ≤ cappedLabelEntropy (certificate750.rho:ℝ) ∧ cappedLabelEntropy (certificate750.rho:ℝ) ≤ (certificate750.bound:ℝ) := rat_label_entropy_certificate_sound certificate750 valid750

def certificate751 : RatLabelEntropyCertificate := ⟨(2752483722447793/500000000000000000),⟨(500000000000000000/2752483722447793),7,10,(5202104422558751803/1000000000000000000)⟩,⟨(500000000000000000/497247516277552207),0,2,(5520175617523551/1000000000000000000)⟩,(17063601360796129/500000000000000000)⟩
theorem valid751 : certificate751.Valid := by decide +kernel
theorem sound751 : 0 ≤ cappedLabelEntropy (certificate751.rho:ℝ) ∧ cappedLabelEntropy (certificate751.rho:ℝ) ≤ (certificate751.bound:ℝ) := rat_label_entropy_certificate_sound certificate751 valid751

def certificate752 : RatLabelEntropyCertificate := ⟨(4503407004783611/1000000000000000000),⟨(1000000000000000000/4503407004783611),7,13,(2701460528248283877/500000000000000000)⟩,⟨(1000000000000000000/995496592995216389),0,2,(902715577870273/200000000000000000)⟩,(5764960788637467/200000000000000000)⟩
theorem valid752 : certificate752.Valid := by decide +kernel
theorem sound752 : 0 ≤ cappedLabelEntropy (certificate752.rho:ℝ) ∧ cappedLabelEntropy (certificate752.rho:ℝ) ≤ (certificate752.bound:ℝ) := rat_label_entropy_certificate_sound certificate752 valid752

def certificate753 : RatLabelEntropyCertificate := ⟨(150836677070383/31250000000000000),⟨(31250000000000000/150836677070383),7,12,(5333577012515963553/1000000000000000000)⟩,⟨(31250000000000000/31099163322929617),0,2,(4838460158799633/1000000000000000000)⟩,(30559075077660361/1000000000000000000)⟩
theorem valid753 : certificate753.Valid := by decide +kernel
theorem sound753 : 0 ≤ cappedLabelEntropy (certificate753.rho:ℝ) ∧ cappedLabelEntropy (certificate753.rho:ℝ) ≤ (certificate753.bound:ℝ) := rat_label_entropy_certificate_sound certificate753 valid753

def certificate754 : RatLabelEntropyCertificate := ⟨(2543847251279747/250000000000000000),⟨(250000000000000000/2543847251279747),6,11,(573472914615369557/125000000000000000)⟩,⟨(250000000000000000/247456152748720253),0,3,(5113756079763761/500000000000000000)⟩,(28402961582817959/500000000000000000)⟩
theorem valid754 : certificate754.Valid := by decide +kernel
theorem sound754 : 0 ≤ cappedLabelEntropy (certificate754.rho:ℝ) ∧ cappedLabelEntropy (certificate754.rho:ℝ) ≤ (certificate754.bound:ℝ) := rat_label_entropy_certificate_sound certificate754 valid754

def certificate755 : RatLabelEntropyCertificate := ⟨(86473861879580829/1000000000000000000),⟨(1000000000000000000/86473861879580829),3,11,(1223956542755421033/500000000000000000)⟩,⟨(1000000000000000000/913526138120419171),0,5,(45221645207391293/500000000000000000)⟩,(36787850982650369/125000000000000000)⟩
theorem valid755 : certificate755.Valid := by decide +kernel
theorem sound755 : 0 ≤ cappedLabelEntropy (certificate755.rho:ℝ) ∧ cappedLabelEntropy (certificate755.rho:ℝ) ≤ (certificate755.bound:ℝ) := rat_label_entropy_certificate_sound certificate755 valid755

def certificate756 : RatLabelEntropyCertificate := ⟨(95236828257366463/1000000000000000000),⟨(1000000000000000000/95236828257366463),3,8,(94055542421984779/40000000000000000)⟩,⟨(1000000000000000000/904763171742633537),0,6,(6255128638177609/62500000000000000)⟩,(314489348928772309/1000000000000000000)⟩
theorem valid756 : certificate756.Valid := by decide +kernel
theorem sound756 : 0 ≤ cappedLabelEntropy (certificate756.rho:ℝ) ∧ cappedLabelEntropy (certificate756.rho:ℝ) ≤ (certificate756.bound:ℝ) := rat_label_entropy_certificate_sound certificate756 valid756

def certificate757 : RatLabelEntropyCertificate := ⟨(1432522209415839/250000000000000000),⟨(250000000000000000/1432522209415839),7,10,(161313257638139483/31250000000000000)⟩,⟨(250000000000000000/248567477790584161),0,2,(5746568781220913/1000000000000000000)⟩,(8823124483573523/250000000000000000)⟩
theorem valid757 : certificate757.Valid := by decide +kernel
theorem sound757 : 0 ≤ cappedLabelEntropy (certificate757.rho:ℝ) ∧ cappedLabelEntropy (certificate757.rho:ℝ) ≤ (certificate757.bound:ℝ) := rat_label_entropy_certificate_sound certificate757 valid757

def certificate758 : RatLabelEntropyCertificate := ⟨(4683299912199121/1000000000000000000),⟨(1000000000000000000/4683299912199121),7,12,(5363752308081195731/1000000000000000000)⟩,⟨(1000000000000000000/995316700087800879),0,2,(93886018440473/20000000000000000)⟩,(29792376816422197/1000000000000000000)⟩
theorem valid758 : certificate758.Valid := by decide +kernel
theorem sound758 : 0 ≤ cappedLabelEntropy (certificate758.rho:ℝ) ∧ cappedLabelEntropy (certificate758.rho:ℝ) ≤ (certificate758.bound:ℝ) := rat_label_entropy_certificate_sound certificate758 valid758

def certificate759 : RatLabelEntropyCertificate := ⟨(5021574737930741/1000000000000000000),⟨(1000000000000000000/5021574737930741),7,11,(5294011701654914599/1000000000000000000)⟩,⟨(1000000000000000000/994978425262069259),0,2,(1006845042465299/200000000000000000)⟩,(31593220897515277/1000000000000000000)⟩
theorem valid759 : certificate759.Valid := by decide +kernel
theorem sound759 : 0 ≤ cappedLabelEntropy (certificate759.rho:ℝ) ∧ cappedLabelEntropy (certificate759.rho:ℝ) ≤ (certificate759.bound:ℝ) := rat_label_entropy_certificate_sound certificate759 valid759

end Cycle12.CutLabelCertificates.Entropy037
