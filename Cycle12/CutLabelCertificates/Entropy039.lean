import Cycle12.RationalLabelEntropy
import Cycle12.RationalMinorityBudget

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CutLabelCertificates.Entropy039

def certificate780 : RatLabelEntropyCertificate := ⟨(11853544167987277/125000000000000000),⟨(125000000000000000/11853544167987277),3,8,(2355686828532335239/1000000000000000000)⟩,⟨(125000000000000000/113146455832012723),0,5,(99630688452935579/1000000000000000000)⟩,(15678438863402801/50000000000000000)⟩
theorem valid780 : certificate780.Valid := by decide +kernel
theorem sound780 : 0 ≤ cappedLabelEntropy (certificate780.rho:ℝ) ∧ cappedLabelEntropy (certificate780.rho:ℝ) ≤ (certificate780.bound:ℝ) := rat_label_entropy_certificate_sound certificate780 valid780

def certificate781 : RatLabelEntropyCertificate := ⟨(6612243111770193/1000000000000000000),⟨(1000000000000000000/6612243111770193),7,7,(5018832331433990959/1000000000000000000)⟩,⟨(1000000000000000000/993387756888229807),0,2,(6634200837994673/1000000000000000000)⟩,(77687643362999/1953125000000000)⟩
theorem valid781 : certificate781.Valid := by decide +kernel
theorem sound781 : 0 ≤ cappedLabelEntropy (certificate781.rho:ℝ) ∧ cappedLabelEntropy (certificate781.rho:ℝ) ≤ (certificate781.bound:ℝ) := rat_label_entropy_certificate_sound certificate781 valid781

def certificate782 : RatLabelEntropyCertificate := ⟨(5452097683831507/1000000000000000000),⟨(1000000000000000000/5452097683831507),7,10,(5211754848244620179/1000000000000000000)⟩,⟨(1000000000000000000/994547902316168493),0,2,(1366753653036979/250000000000000000)⟩,(33852204451255673/1000000000000000000)⟩
theorem valid782 : certificate782.Valid := by decide +kernel
theorem sound782 : 0 ≤ cappedLabelEntropy (certificate782.rho:ℝ) ∧ cappedLabelEntropy (certificate782.rho:ℝ) ≤ (certificate782.bound:ℝ) := rat_label_entropy_certificate_sound certificate782 valid782

def certificate783 : RatLabelEntropyCertificate := ⟨(580043379905999/100000000000000000),⟨(100000000000000000/580043379905999),7,9,(2574911285642619199/500000000000000000)⟩,⟨(100000000000000000/99419956620094001),0,2,(5817321651432687/1000000000000000000)⟩,(7130956712790127/200000000000000000)⟩
theorem valid783 : certificate783.Valid := by decide +kernel
theorem sound783 : 0 ≤ cappedLabelEntropy (certificate783.rho:ℝ) ∧ cappedLabelEntropy (certificate783.rho:ℝ) ≤ (certificate783.bound:ℝ) := rat_label_entropy_certificate_sound certificate783 valid783

def certificate784 : RatLabelEntropyCertificate := ⟨(556261834255769/50000000000000000),⟨(50000000000000000/556261834255769),6,9,(89970783521791863/20000000000000000)⟩,⟨(50000000000000000/49443738165744231),0,3,(11187584988465571/1000000000000000000)⟩,(30555216764397353/500000000000000000)⟩
theorem valid784 : certificate784.Valid := by decide +kernel
theorem sound784 : 0 ≤ cappedLabelEntropy (certificate784.rho:ℝ) ∧ cappedLabelEntropy (certificate784.rho:ℝ) ≤ (certificate784.bound:ℝ) := rat_label_entropy_certificate_sound certificate784 valid784

def certificate785 : RatLabelEntropyCertificate := ⟨(8524832579752623/100000000000000000),⟨(100000000000000000/8524832579752623),3,10,(615546700437512171/250000000000000000)⟩,⟨(100000000000000000/91475167420247377),0,5,(89102644854953483/1000000000000000000)⟩,(291404096206894411/1000000000000000000)⟩
theorem valid785 : certificate785.Valid := by decide +kernel
theorem sound785 : 0 ≤ cappedLabelEntropy (certificate785.rho:ℝ) ∧ cappedLabelEntropy (certificate785.rho:ℝ) ≤ (certificate785.bound:ℝ) := rat_label_entropy_certificate_sound certificate785 valid785

def certificate786 : RatLabelEntropyCertificate := ⟨(47366075354514881/500000000000000000),⟨(500000000000000000/47366075354514881),3,9,(471340367156813281/200000000000000000)⟩,⟨(500000000000000000/452633924645485119),0,5,(24881103251039283/250000000000000000)⟩,(156675842397981443/500000000000000000)⟩
theorem valid786 : certificate786.Valid := by decide +kernel
theorem sound786 : 0 ≤ cappedLabelEntropy (certificate786.rho:ℝ) ∧ cappedLabelEntropy (certificate786.rho:ℝ) ≤ (certificate786.bound:ℝ) := rat_label_entropy_certificate_sound certificate786 valid786

def certificate787 : RatLabelEntropyCertificate := ⟨(3476918385075233/500000000000000000),⟨(500000000000000000/3476918385075233),7,6,(621057714808964787/125000000000000000)⟩,⟨(500000000000000000/496523081614924767),0,3,(6978127367125929/1000000000000000000)⟩,(41479474397447223/1000000000000000000)⟩
theorem valid787 : certificate787.Valid := by decide +kernel
theorem sound787 : 0 ≤ cappedLabelEntropy (certificate787.rho:ℝ) ∧ cappedLabelEntropy (certificate787.rho:ℝ) ≤ (certificate787.bound:ℝ) := rat_label_entropy_certificate_sound certificate787 valid787

def certificate788 : RatLabelEntropyCertificate := ⟨(113103981016309/20000000000000000),⟨(20000000000000000/113103981016309),7,9,(2587589985475167301/500000000000000000)⟩,⟨(20000000000000000/19886896018983691),0,2,(5671250232658239/1000000000000000000)⟩,(17452925521621517/500000000000000000)⟩
theorem valid788 : certificate788.Valid := by decide +kernel
theorem sound788 : 0 ≤ cappedLabelEntropy (certificate788.rho:ℝ) ∧ cappedLabelEntropy (certificate788.rho:ℝ) ≤ (certificate788.bound:ℝ) := rat_label_entropy_certificate_sound certificate788 valid788

def certificate789 : RatLabelEntropyCertificate := ⟨(5990746208880547/1000000000000000000),⟨(1000000000000000000/5990746208880547),7,8,(1279384824710162517/250000000000000000)⟩,⟨(1000000000000000000/994009253791119453),0,2,(1502190679970999/250000000000000000)⟩,(18315322450363313/500000000000000000)⟩
theorem valid789 : certificate789.Valid := by decide +kernel
theorem sound789 : 0 ≤ cappedLabelEntropy (certificate789.rho:ℝ) ∧ cappedLabelEntropy (certificate789.rho:ℝ) ≤ (certificate789.bound:ℝ) := rat_label_entropy_certificate_sound certificate789 valid789

def certificate790 : RatLabelEntropyCertificate := ⟨(11008962608655881/1000000000000000000),⟨(1000000000000000000/11008962608655881),6,10,(2254522777666919933/500000000000000000)⟩,⟨(1000000000000000000/988991037391344119),0,3,(2767502423594107/250000000000000000)⟩,(7573506786371227/125000000000000000)⟩
theorem valid790 : certificate790.Valid := by decide +kernel
theorem sound790 : 0 ≤ cappedLabelEntropy (certificate790.rho:ℝ) ∧ cappedLabelEntropy (certificate790.rho:ℝ) ≤ (certificate790.bound:ℝ) := rat_label_entropy_certificate_sound certificate790 valid790

def certificate791 : RatLabelEntropyCertificate := ⟨(81521501391337919/1000000000000000000),⟨(1000000000000000000/81521501391337919),3,11,(2506888472777282727/1000000000000000000)⟩,⟨(1000000000000000000/918478498608662081),0,5,(85036783845745511/1000000000000000000)⟩,(35308721209323989/125000000000000000)⟩
theorem valid791 : certificate791.Valid := by decide +kernel
theorem sound791 : 0 ≤ cappedLabelEntropy (certificate791.rho:ℝ) ∧ cappedLabelEntropy (certificate791.rho:ℝ) ≤ (certificate791.bound:ℝ) := rat_label_entropy_certificate_sound certificate791 valid791

def certificate792 : RatLabelEntropyCertificate := ⟨(94615545310799071/1000000000000000000),⟨(1000000000000000000/94615545310799071),3,9,(2357933489671833451/1000000000000000000)⟩,⟨(1000000000000000000/905384454689200929),0,6,(49697806838965129/500000000000000000)⟩,(313088406420187299/1000000000000000000)⟩
theorem valid792 : certificate792.Valid := by decide +kernel
theorem sound792 : 0 ≤ cappedLabelEntropy (certificate792.rho:ℝ) ∧ cappedLabelEntropy (certificate792.rho:ℝ) ≤ (certificate792.bound:ℝ) := rat_label_entropy_certificate_sound certificate792 valid792

def certificate793 : RatLabelEntropyCertificate := ⟨(7219858902679457/1000000000000000000),⟨(1000000000000000000/7219858902679457),7,5,(2465459934416766383/500000000000000000)⟩,⟨(1000000000000000000/992780141097320543),0,3,(7246048215531061/1000000000000000000)⟩,(42794278483209717/1000000000000000000)⟩
theorem valid793 : certificate793.Valid := by decide +kernel
theorem sound793 : 0 ≤ cappedLabelEntropy (certificate793.rho:ℝ) ∧ cappedLabelEntropy (certificate793.rho:ℝ) ≤ (certificate793.bound:ℝ) := rat_label_entropy_certificate_sound certificate793 valid793

def certificate794 : RatLabelEntropyCertificate := ⟨(5863756896461481/1000000000000000000),⟨(1000000000000000000/5863756896461481),7,9,(5138964772204373239/1000000000000000000)⟩,⟨(1000000000000000000/994136243103538519),0,3,(58810162216623/10000000000000000)⟩,(8995042873980081/250000000000000000)⟩
theorem valid794 : certificate794.Valid := by decide +kernel
theorem sound794 : 0 ≤ cappedLabelEntropy (certificate794.rho:ℝ) ∧ cappedLabelEntropy (certificate794.rho:ℝ) ≤ (certificate794.bound:ℝ) := rat_label_entropy_certificate_sound certificate794 valid794

def certificate795 : RatLabelEntropyCertificate := ⟨(6213506465413223/1000000000000000000),⟨(1000000000000000000/6213506465413223),7,8,(5081029894175880059/1000000000000000000)⟩,⟨(1000000000000000000/993786493534586777),0,2,(1558222658549499/250000000000000000)⟩,(37765174626363889/1000000000000000000)⟩
theorem valid795 : certificate795.Valid := by decide +kernel
theorem sound795 : 0 ≤ cappedLabelEntropy (certificate795.rho:ℝ) ∧ cappedLabelEntropy (certificate795.rho:ℝ) ≤ (certificate795.bound:ℝ) := rat_label_entropy_certificate_sound certificate795 valid795

def certificate796 : RatLabelEntropyCertificate := ⟨(91552996150163/8000000000000000),⟨(8000000000000000/91552996150163),6,9,(4470278823150009507/1000000000000000000)⟩,⟨(8000000000000000/7908447003849837),0,3,(11510112444208311/1000000000000000000)⟩,(7817102096240343/125000000000000000)⟩
theorem valid796 : certificate796.Valid := by decide +kernel
theorem sound796 : 0 ≤ cappedLabelEntropy (certificate796.rho:ℝ) ∧ cappedLabelEntropy (certificate796.rho:ℝ) ≤ (certificate796.bound:ℝ) := rat_label_entropy_certificate_sound certificate796 valid796

def certificate797 : RatLabelEntropyCertificate := ⟨(8413316468765619/100000000000000000),⟨(100000000000000000/8413316468765619),3,11,(2475354441490076557/1000000000000000000)⟩,⟨(100000000000000000/91586683531234381),0,5,(21971075293183183/250000000000000000)⟩,(288749719674913453/1000000000000000000)⟩
theorem valid797 : certificate797.Valid := by decide +kernel
theorem sound797 : 0 ≤ cappedLabelEntropy (certificate797.rho:ℝ) ∧ cappedLabelEntropy (certificate797.rho:ℝ) ≤ (certificate797.bound:ℝ) := rat_label_entropy_certificate_sound certificate797 valid797

def certificate798 : RatLabelEntropyCertificate := ⟨(18902493852013423/200000000000000000),⟨(200000000000000000/18902493852013423),3,9,(1179511751672537311/500000000000000000)⟩,⟨(200000000000000000/181097506147986577),0,5,(3102555385417143/31250000000000000)⟩,(156427771610642593/500000000000000000)⟩
theorem valid798 : certificate798.Valid := by decide +kernel
theorem sound798 : 0 ≤ cappedLabelEntropy (certificate798.rho:ℝ) ∧ cappedLabelEntropy (certificate798.rho:ℝ) ≤ (certificate798.bound:ℝ) := rat_label_entropy_certificate_sound certificate798 valid798

def certificate799 : RatLabelEntropyCertificate := ⟨(7438403219436779/1000000000000000000),⟨(1000000000000000000/7438403219436779),7,4,(2450549537107486109/500000000000000000)⟩,⟨(1000000000000000000/992561596780563221),0,3,(7466206099154311/1000000000000000000)⟩,(877340411601773/20000000000000000)⟩
theorem valid799 : certificate799.Valid := by decide +kernel
theorem sound799 : 0 ≤ cappedLabelEntropy (certificate799.rho:ℝ) ∧ cappedLabelEntropy (certificate799.rho:ℝ) ≤ (certificate799.bound:ℝ) := rat_label_entropy_certificate_sound certificate799 valid799

end Cycle12.CutLabelCertificates.Entropy039
