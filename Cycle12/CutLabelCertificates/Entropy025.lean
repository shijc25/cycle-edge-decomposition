import Cycle12.RationalLabelEntropy
import Cycle12.RationalMinorityBudget

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CutLabelCertificates.Entropy025

def certificate500 : RatLabelEntropyCertificate := ⟨(5291116609874271/250000000000000000),⟨(250000000000000000/5291116609874271),5,10,(2409644759309273/625000000000000)⟩,⟨(250000000000000000/244708883390125729),0,3,(21391644884474807/1000000000000000000)⟩,(1281713189468119/12500000000000000)⟩
theorem valid500 : certificate500.Valid := by decide +kernel
theorem sound500 : 0 ≤ cappedLabelEntropy (certificate500.rho:ℝ) ∧ cappedLabelEntropy (certificate500.rho:ℝ) ≤ (certificate500.bound:ℝ) := rat_label_entropy_certificate_sound certificate500 valid500

def certificate501 : RatLabelEntropyCertificate := ⟨(46517219741239967/500000000000000000),⟨(500000000000000000/46517219741239967),3,9,(1187392768681695457/500000000000000000)⟩,⟨(500000000000000000/453482780258760033),0,5,(97650800351392079/1000000000000000000)⟩,(61900550847077549/200000000000000000)⟩
theorem valid501 : certificate501.Valid := by decide +kernel
theorem sound501 : 0 ≤ cappedLabelEntropy (certificate501.rho:ℝ) ∧ cappedLabelEntropy (certificate501.rho:ℝ) ≤ (certificate501.bound:ℝ) := rat_label_entropy_certificate_sound certificate501 valid501

def certificate502 : RatLabelEntropyCertificate := ⟨(824035903360659/1000000000000000000),⟨(1000000000000000000/824035903360659),10,7,(7101296456964401443/1000000000000000000)⟩,⟨(1000000000000000000/999175964096639341),0,2,(32975024303099/40000000000000000)⟩,(1335083906685097/200000000000000000)⟩
theorem valid502 : certificate502.Valid := by decide +kernel
theorem sound502 : 0 ≤ cappedLabelEntropy (certificate502.rho:ℝ) ∧ cappedLabelEntropy (certificate502.rho:ℝ) ≤ (certificate502.bound:ℝ) := rat_label_entropy_certificate_sound certificate502 valid502

def certificate503 : RatLabelEntropyCertificate := ⟨(83682214026619/125000000000000000),⟨(125000000000000000/83682214026619),10,10,(3654521279032371843/500000000000000000)⟩,⟨(125000000000000000/124916317785973381),0,2,(5231889836629/7812500000000000)⟩,(1390582121191391/250000000000000000)⟩
theorem valid503 : certificate503.Valid := by decide +kernel
theorem sound503 : 0 ≤ cappedLabelEntropy (certificate503.rho:ℝ) ∧ cappedLabelEntropy (certificate503.rho:ℝ) ≤ (certificate503.bound:ℝ) := rat_label_entropy_certificate_sound certificate503 valid503

def certificate504 : RatLabelEntropyCertificate := ⟨(18167026144513/20000000000000000),⟨(20000000000000000/18167026144513),10,5,(7003879351959456913/1000000000000000000)⟩,⟨(20000000000000000/19981832973855487),0,2,(181752821654433/200000000000000000)⟩,(227185049881549/31250000000000000)⟩
theorem valid504 : certificate504.Valid := by decide +kernel
theorem sound504 : 0 ≤ cappedLabelEntropy (certificate504.rho:ℝ) ∧ cappedLabelEntropy (certificate504.rho:ℝ) ≤ (certificate504.bound:ℝ) := rat_label_entropy_certificate_sound certificate504 valid504

def certificate505 : RatLabelEntropyCertificate := ⟨(2319851721180169/100000000000000000),⟨(100000000000000000/2319851721180169),5,9,(470458364454602961/125000000000000000)⟩,⟨(100000000000000000/97680148278819831),0,3,(23471838180858273/1000000000000000000)⟩,(55119409030358221/500000000000000000)⟩
theorem valid505 : certificate505.Valid := by decide +kernel
theorem sound505 : 0 ≤ cappedLabelEntropy (certificate505.rho:ℝ) ∧ cappedLabelEntropy (certificate505.rho:ℝ) ≤ (certificate505.bound:ℝ) := rat_label_entropy_certificate_sound certificate505 valid505

def certificate506 : RatLabelEntropyCertificate := ⟨(92891944979596067/1000000000000000000),⟨(1000000000000000000/92891944979596067),3,9,(37129974113700321/15625000000000000)⟩,⟨(1000000000000000000/907108055020403933),0,5,(97493701431087593/1000000000000000000)⟩,(77294538669892283/250000000000000000)⟩
theorem valid506 : certificate506.Valid := by decide +kernel
theorem sound506 : 0 ≤ cappedLabelEntropy (certificate506.rho:ℝ) ∧ cappedLabelEntropy (certificate506.rho:ℝ) ≤ (certificate506.bound:ℝ) := rat_label_entropy_certificate_sound certificate506 valid506

def certificate507 : RatLabelEntropyCertificate := ⟨(905092571176711/1000000000000000000),⟨(1000000000000000000/905092571176711),10,5,(7007473330902418569/1000000000000000000)⟩,⟨(1000000000000000000/999094907428823289),0,2,(905502414774169/1000000000000000000)⟩,(1811773726446019/250000000000000000)⟩
theorem valid507 : certificate507.Valid := by decide +kernel
theorem sound507 : 0 ≤ cappedLabelEntropy (certificate507.rho:ℝ) ∧ cappedLabelEntropy (certificate507.rho:ℝ) ≤ (certificate507.bound:ℝ) := rat_label_entropy_certificate_sound certificate507 valid507

def certificate508 : RatLabelEntropyCertificate := ⟨(364932548733367/500000000000000000),⟨(500000000000000000/364932548733367),10,9,(3611325419444932629/500000000000000000)⟩,⟨(500000000000000000/499635067451266633),0,2,(365065789334213/500000000000000000)⟩,(3000579719803569/500000000000000000)⟩
theorem valid508 : certificate508.Valid := by decide +kernel
theorem sound508 : 0 ≤ cappedLabelEntropy (certificate508.rho:ℝ) ∧ cappedLabelEntropy (certificate508.rho:ℝ) ≤ (certificate508.bound:ℝ) := rat_label_entropy_certificate_sound certificate508 valid508

def certificate509 : RatLabelEntropyCertificate := ⟨(975636509473667/1000000000000000000),⟨(1000000000000000000/975636509473667),10,2,(346621023486899091/50000000000000000)⟩,⟨(1000000000000000000/999024363490526333),0,2,(244028188139567/250000000000000000)⟩,(7738682930618473/1000000000000000000)⟩
theorem valid509 : certificate509.Valid := by decide +kernel
theorem sound509 : 0 ≤ cappedLabelEntropy (certificate509.rho:ℝ) ∧ cappedLabelEntropy (certificate509.rho:ℝ) ≤ (certificate509.bound:ℝ) := rat_label_entropy_certificate_sound certificate509 valid509

def certificate510 : RatLabelEntropyCertificate := ⟨(25268200602054721/1000000000000000000),⟨(1000000000000000000/25268200602054721),5,7,(1839104283500417183/500000000000000000)⟩,⟨(1000000000000000000/974731799397945279),0,4,(1599557710351567/62500000000000000)⟩,(2947198704280069/25000000000000000)⟩
theorem valid510 : certificate510.Valid := by decide +kernel
theorem sound510 : 0 ≤ cappedLabelEntropy (certificate510.rho:ℝ) ∧ cappedLabelEntropy (certificate510.rho:ℝ) ≤ (certificate510.bound:ℝ) := rat_label_entropy_certificate_sound certificate510 valid510

def certificate511 : RatLabelEntropyCertificate := ⟨(1850260988122921/20000000000000000),⟨(20000000000000000/1850260988122921),3,9,(476081113950562673/200000000000000000)⟩,⟨(20000000000000000/18149739011877079),0,5,(12134511557177763/125000000000000000)⟩,(19269616575060017/62500000000000000)⟩
theorem valid511 : certificate511.Valid := by decide +kernel
theorem sound511 : 0 ≤ cappedLabelEntropy (certificate511.rho:ℝ) ∧ cappedLabelEntropy (certificate511.rho:ℝ) ≤ (certificate511.bound:ℝ) := rat_label_entropy_certificate_sound certificate511 valid511

def certificate512 : RatLabelEntropyCertificate := ⟨(24571384614283/25000000000000000),⟨(25000000000000000/24571384614283),9,16,(6925048565047397081/1000000000000000000)⟩,⟨(25000000000000000/24975428615385717),0,2,(491669351819631/500000000000000000)⟩,(389434674723713/50000000000000000)⟩
theorem valid512 : certificate512.Valid := by decide +kernel
theorem sound512 : 0 ≤ cappedLabelEntropy (certificate512.rho:ℝ) ∧ cappedLabelEntropy (certificate512.rho:ℝ) ≤ (certificate512.bound:ℝ) := rat_label_entropy_certificate_sound certificate512 valid512

def certificate513 : RatLabelEntropyCertificate := ⟨(795778307139809/1000000000000000000),⟨(1000000000000000000/795778307139809),10,7,(713618991952894927/100000000000000000)⟩,⟨(1000000000000000000/999204221692860191),0,2,(398047553388101/500000000000000000)⟩,(6474286725150727/1000000000000000000)⟩
theorem valid513 : certificate513.Valid := by decide +kernel
theorem sound513 : 0 ≤ cappedLabelEntropy (certificate513.rho:ℝ) ∧ cappedLabelEntropy (certificate513.rho:ℝ) ≤ (certificate513.bound:ℝ) := rat_label_entropy_certificate_sound certificate513 valid513

def certificate514 : RatLabelEntropyCertificate := ⟨(32780475947707/31250000000000000),⟨(31250000000000000/32780475947707),9,14,(3429970781250060657/500000000000000000)⟩,⟨(31250000000000000/31217219524052293),0,2,(65595361868299/62500000000000000)⟩,(1030541705485793/125000000000000000)⟩
theorem valid514 : certificate514.Valid := by decide +kernel
theorem sound514 : 0 ≤ cappedLabelEntropy (certificate514.rho:ℝ) ∧ cappedLabelEntropy (certificate514.rho:ℝ) ≤ (certificate514.bound:ℝ) := rat_label_entropy_certificate_sound certificate514 valid514

def certificate515 : RatLabelEntropyCertificate := ⟨(24352553721017289/1000000000000000000),⟨(1000000000000000000/24352553721017289),5,8,(232194909959133793/62500000000000000)⟩,⟨(1000000000000000000/975647446278982711),0,4,(12326990450313779/500000000000000000)⟩,(5726310890136667/50000000000000000)⟩
theorem valid515 : certificate515.Valid := by decide +kernel
theorem sound515 : 0 ≤ cappedLabelEntropy (certificate515.rho:ℝ) ∧ cappedLabelEntropy (certificate515.rho:ℝ) ≤ (certificate515.bound:ℝ) := rat_label_entropy_certificate_sound certificate515 valid515

def certificate516 : RatLabelEntropyCertificate := ⟨(92614130275052107/1000000000000000000),⟨(1000000000000000000/92614130275052107),3,9,(1189656777104209109/500000000000000000)⟩,⟨(1000000000000000000/907385869724947893),0,5,(3887499365619857/40000000000000000)⟩,(308544605297859627/1000000000000000000)⟩
theorem valid516 : certificate516.Valid := by decide +kernel
theorem sound516 : 0 ≤ cappedLabelEntropy (certificate516.rho:ℝ) ∧ cappedLabelEntropy (certificate516.rho:ℝ) ≤ (certificate516.bound:ℝ) := rat_label_entropy_certificate_sound certificate516 valid516

def certificate517 : RatLabelEntropyCertificate := ⟨(1061306059734253/1000000000000000000),⟨(1000000000000000000/1061306059734253),9,15,(6848254997484866893/1000000000000000000)⟩,⟨(1000000000000000000/998938693940265747),0,2,(530934821901273/500000000000000000)⟩,(4164418601275501/500000000000000000)⟩
theorem valid517 : certificate517.Valid := by decide +kernel
theorem sound517 : 0 ≤ cappedLabelEntropy (certificate517.rho:ℝ) ∧ cappedLabelEntropy (certificate517.rho:ℝ) ≤ (certificate517.bound:ℝ) := rat_label_entropy_certificate_sound certificate517 valid517

def certificate518 : RatLabelEntropyCertificate := ⟨(217055177872047/250000000000000000),⟨(250000000000000000/217055177872047),10,6,(7049064599718512821/1000000000000000000)⟩,⟨(250000000000000000/249782944822127953),0,2,(868597833389281/1000000000000000000)⟩,(3493993790427093/500000000000000000)⟩
theorem valid518 : certificate518.Valid := by decide +kernel
theorem sound518 : 0 ≤ cappedLabelEntropy (certificate518.rho:ℝ) ∧ cappedLabelEntropy (certificate518.rho:ℝ) ≤ (certificate518.bound:ℝ) := rat_label_entropy_certificate_sound certificate518 valid518

def certificate519 : RatLabelEntropyCertificate := ⟨(1065861643256481/1000000000000000000),⟨(1000000000000000000/1065861643256481),9,14,(1368794350445632313/200000000000000000)⟩,⟨(1000000000000000000/998934138356743519),0,2,(1066430077728661/1000000000000000000)⟩,(8360020389044441/1000000000000000000)⟩
theorem valid519 : certificate519.Valid := by decide +kernel
theorem sound519 : 0 ≤ cappedLabelEntropy (certificate519.rho:ℝ) ∧ cappedLabelEntropy (certificate519.rho:ℝ) ≤ (certificate519.bound:ℝ) := rat_label_entropy_certificate_sound certificate519 valid519

end Cycle12.CutLabelCertificates.Entropy025
