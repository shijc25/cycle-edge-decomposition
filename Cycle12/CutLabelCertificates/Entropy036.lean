import Cycle12.RationalLabelEntropy
import Cycle12.RationalMinorityBudget

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CutLabelCertificates.Entropy036

def certificate720 : RatLabelEntropyCertificate := ⟨(48023437679910553/500000000000000000),⟨(500000000000000000/48023437679910553),3,8,(2342918921688492201/1000000000000000000)⟩,⟨(500000000000000000/451976562320089447),0,6,(50488886604263221/500000000000000000)⟩,(316309215260635897/1000000000000000000)⟩
theorem valid720 : certificate720.Valid := by decide +kernel
theorem sound720 : 0 ≤ cappedLabelEntropy (certificate720.rho:ℝ) ∧ cappedLabelEntropy (certificate720.rho:ℝ) ≤ (certificate720.bound:ℝ) := rat_label_entropy_certificate_sound certificate720 valid720

def certificate721 : RatLabelEntropyCertificate := ⟨(449021492845891/100000000000000000),⟨(100000000000000000/449021492845891),7,13,(5405854710119967633/1000000000000000000)⟩,⟨(100000000000000000/99550978507154109),0,2,(2250163111393469/500000000000000000)⟩,(14376784155629519/500000000000000000)⟩
theorem valid721 : certificate721.Valid := by decide +kernel
theorem sound721 : 0 ≤ cappedLabelEntropy (certificate721.rho:ℝ) ∧ cappedLabelEntropy (certificate721.rho:ℝ) ≤ (certificate721.bound:ℝ) := rat_label_entropy_certificate_sound certificate721 valid721

def certificate722 : RatLabelEntropyCertificate := ⟨(457782226397499/125000000000000000),⟨(125000000000000000/457782226397499),8,5,(5609675433465689247/1000000000000000000)⟩,⟨(125000000000000000/124542217773602501),0,2,(458622536914581/125000000000000000)⟩,(3024952652245661/125000000000000000)⟩
theorem valid722 : certificate722.Valid := by decide +kernel
theorem sound722 : 0 ≤ cappedLabelEntropy (certificate722.rho:ℝ) ∧ cappedLabelEntropy (certificate722.rho:ℝ) ≤ (certificate722.bound:ℝ) := rat_label_entropy_certificate_sound certificate722 valid722

def certificate723 : RatLabelEntropyCertificate := ⟨(992845355358661/250000000000000000),⟨(250000000000000000/992845355358661),7,15,(5528641279711964503/1000000000000000000)⟩,⟨(250000000000000000/249007154644641339),0,2,(1989644148861233/500000000000000000)⟩,(2591982829013111/100000000000000000)⟩
theorem valid723 : certificate723.Valid := by decide +kernel
theorem sound723 : 0 ≤ cappedLabelEntropy (certificate723.rho:ℝ) ∧ cappedLabelEntropy (certificate723.rho:ℝ) ≤ (certificate723.bound:ℝ) := rat_label_entropy_certificate_sound certificate723 valid723

def certificate724 : RatLabelEntropyCertificate := ⟨(9622537860104223/1000000000000000000),⟨(1000000000000000000/9622537860104223),6,12,(185745889530993323/40000000000000000)⟩,⟨(1000000000000000000/990377462139895777),0,3,(483456681575907/50000000000000000)⟩,(54259763386342447/1000000000000000000)⟩
theorem valid724 : certificate724.Valid := by decide +kernel
theorem sound724 : 0 ≤ cappedLabelEntropy (certificate724.rho:ℝ) ∧ cappedLabelEntropy (certificate724.rho:ℝ) ≤ (certificate724.bound:ℝ) := rat_label_entropy_certificate_sound certificate724 valid724

def certificate725 : RatLabelEntropyCertificate := ⟨(89999136764177883/1000000000000000000),⟨(1000000000000000000/89999136764177883),3,9,(2407955200207005437/1000000000000000000)⟩,⟨(1000000000000000000/910000863235822117),0,5,(94309730860897723/1000000000000000000)⟩,(1512679129401993/5000000000000000)⟩
theorem valid725 : certificate725.Valid := by decide +kernel
theorem sound725 : 0 ≤ cappedLabelEntropy (certificate725.rho:ℝ) ∧ cappedLabelEntropy (certificate725.rho:ℝ) ≤ (certificate725.bound:ℝ) := rat_label_entropy_certificate_sound certificate725 valid725

def certificate726 : RatLabelEntropyCertificate := ⟨(19182179502269991/200000000000000000),⟨(200000000000000000/19182179502269991),3,8,(1172167834718257851/500000000000000000)⟩,⟨(200000000000000000/180817820497730009),0,5,(1008273587473073/10000000000000000)⟩,(3950053179996023/12500000000000000)⟩
theorem valid726 : certificate726.Valid := by decide +kernel
theorem sound726 : 0 ≤ cappedLabelEntropy (certificate726.rho:ℝ) ∧ cappedLabelEntropy (certificate726.rho:ℝ) ≤ (certificate726.bound:ℝ) := rat_label_entropy_certificate_sound certificate726 valid726

def certificate727 : RatLabelEntropyCertificate := ⟨(4679912748204081/1000000000000000000),⟨(1000000000000000000/4679912748204081),7,12,(670559476596563911/125000000000000000)⟩,⟨(1000000000000000000/995320087251795919),0,2,(4690897826073063/1000000000000000000)⟩,(14887111788581413/500000000000000000)⟩
theorem valid727 : certificate727.Valid := by decide +kernel
theorem sound727 : 0 ≤ cappedLabelEntropy (certificate727.rho:ℝ) ∧ cappedLabelEntropy (certificate727.rho:ℝ) ≤ (certificate727.bound:ℝ) := rat_label_entropy_certificate_sound certificate727 valid727

def certificate728 : RatLabelEntropyCertificate := ⟨(1911551040801403/500000000000000000),⟨(500000000000000000/1911551040801403),8,3,(5566693122661808293/1000000000000000000)⟩,⟨(500000000000000000/498088448959198597),0,2,(957607204057609/250000000000000000)⟩,(12548910380371029/500000000000000000)⟩
theorem valid728 : certificate728.Valid := by decide +kernel
theorem sound728 : 0 ≤ cappedLabelEntropy (certificate728.rho:ℝ) ∧ cappedLabelEntropy (certificate728.rho:ℝ) ≤ (certificate728.bound:ℝ) := rat_label_entropy_certificate_sound certificate728 valid728

def certificate729 : RatLabelEntropyCertificate := ⟨(829483968357019/200000000000000000),⟨(200000000000000000/829483968357019),7,15,(2742634431480822071/500000000000000000)⟩,⟨(200000000000000000/199170516031642981),0,2,(831208848344391/200000000000000000)⟩,(26888520301143591/1000000000000000000)⟩
theorem valid729 : certificate729.Valid := by decide +kernel
theorem sound729 : 0 ≤ cappedLabelEntropy (certificate729.rho:ℝ) ∧ cappedLabelEntropy (certificate729.rho:ℝ) ≤ (certificate729.bound:ℝ) := rat_label_entropy_certificate_sound certificate729 valid729

def certificate730 : RatLabelEntropyCertificate := ⟨(9922423587054861/1000000000000000000),⟨(1000000000000000000/9922423587054861),6,11,(4612958074313792659/1000000000000000000)⟩,⟨(1000000000000000000/990077576412945139),0,3,(9971978910410993/1000000000000000000)⟩,(6955594589290883/125000000000000000)⟩
theorem valid730 : certificate730.Valid := by decide +kernel
theorem sound730 : 0 ≤ cappedLabelEntropy (certificate730.rho:ℝ) ∧ cappedLabelEntropy (certificate730.rho:ℝ) ≤ (certificate730.bound:ℝ) := rat_label_entropy_certificate_sound certificate730 valid730

def certificate731 : RatLabelEntropyCertificate := ⟨(5675525698750401/62500000000000000),⟨(62500000000000000/5675525698750401),3,9,(2399003363524126713/1000000000000000000)⟩,⟨(62500000000000000/56824474301249599),0,5,(95199438234405929/1000000000000000000)⟩,(76101053090056919/250000000000000000)⟩
theorem valid731 : certificate731.Valid := by decide +kernel
theorem sound731 : 0 ≤ cappedLabelEntropy (certificate731.rho:ℝ) ∧ cappedLabelEntropy (certificate731.rho:ℝ) ≤ (certificate731.bound:ℝ) := rat_label_entropy_certificate_sound certificate731 valid731

def certificate732 : RatLabelEntropyCertificate := ⟨(11972428291570069/125000000000000000),⟨(125000000000000000/11972428291570069),3,8,(2345707373513877807/1000000000000000000)⟩,⟨(125000000000000000/113027571708429931),0,5,(2013639018655117/20000000000000000)⟩,(78927299502397511/250000000000000000)⟩
theorem valid732 : certificate732.Valid := by decide +kernel
theorem sound732 : 0 ≤ cappedLabelEntropy (certificate732.rho:ℝ) ∧ cappedLabelEntropy (certificate732.rho:ℝ) ≤ (certificate732.bound:ℝ) := rat_label_entropy_certificate_sound certificate732 valid732

def certificate733 : RatLabelEntropyCertificate := ⟨(4886938604044481/1000000000000000000),⟨(1000000000000000000/4886938604044481),7,12,(5321189223890596577/1000000000000000000)⟩,⟨(1000000000000000000/995113061395955519),0,2,(76545605237781/15625000000000000)⟩,(15439651528894609/500000000000000000)⟩
theorem valid733 : certificate733.Valid := by decide +kernel
theorem sound733 : 0 ≤ cappedLabelEntropy (certificate733.rho:ℝ) ∧ cappedLabelEntropy (certificate733.rho:ℝ) ≤ (certificate733.bound:ℝ) := rat_label_entropy_certificate_sound certificate733 valid733

def certificate734 : RatLabelEntropyCertificate := ⟨(3986599836334397/1000000000000000000),⟨(1000000000000000000/3986599836334397),7,15,(5524816582729541109/1000000000000000000)⟩,⟨(1000000000000000000/996013400163665603),0,2,(998641877114713/250000000000000000)⟩,(5200775130154111/200000000000000000)⟩
theorem valid734 : certificate734.Valid := by decide +kernel
theorem sound734 : 0 ≤ cappedLabelEntropy (certificate734.rho:ℝ) ∧ cappedLabelEntropy (certificate734.rho:ℝ) ≤ (certificate734.bound:ℝ) := rat_label_entropy_certificate_sound certificate734 valid734

def certificate735 : RatLabelEntropyCertificate := ⟨(4307041904180651/1000000000000000000),⟨(1000000000000000000/4307041904180651),7,14,(1089500788727525961/200000000000000000)⟩,⟨(1000000000000000000/995692958095819349),0,2,(2158171964121553/500000000000000000)⟩,(27760381012507931/1000000000000000000)⟩
theorem valid735 : certificate735.Valid := by decide +kernel
theorem sound735 : 0 ≤ cappedLabelEntropy (certificate735.rho:ℝ) ∧ cappedLabelEntropy (certificate735.rho:ℝ) ≤ (certificate735.bound:ℝ) := rat_label_entropy_certificate_sound certificate735 valid735

def certificate736 : RatLabelEntropyCertificate := ⟨(4957649130412651/500000000000000000),⟨(500000000000000000/4957649130412651),6,11,(4613676435685185211/1000000000000000000)⟩,⟨(500000000000000000/495042350869587349),0,3,(9964782201021863/1000000000000000000)⟩,(13902989088038641/250000000000000000)⟩
theorem valid736 : certificate736.Valid := by decide +kernel
theorem sound736 : 0 ≤ cappedLabelEntropy (certificate736.rho:ℝ) ∧ cappedLabelEntropy (certificate736.rho:ℝ) ≤ (certificate736.bound:ℝ) := rat_label_entropy_certificate_sound certificate736 valid736

def certificate737 : RatLabelEntropyCertificate := ⟨(44464203609474579/500000000000000000),⟨(500000000000000000/44464203609474579),3,10,(1209961823117098787/500000000000000000)⟩,⟨(500000000000000000/455535796390525421),0,5,(93133797783576833/1000000000000000000)⟩,(37506439117438829/125000000000000000)⟩
theorem valid737 : certificate737.Valid := by decide +kernel
theorem sound737 : 0 ≤ cappedLabelEntropy (certificate737.rho:ℝ) ∧ cappedLabelEntropy (certificate737.rho:ℝ) ≤ (certificate737.bound:ℝ) := rat_label_entropy_certificate_sound certificate737 valid737

def certificate738 : RatLabelEntropyCertificate := ⟨(95651005773258921/1000000000000000000),⟨(1000000000000000000/95651005773258921),3,8,(1173524534004963021/500000000000000000)⟩,⟨(1000000000000000000/904348994226741079),0,5,(25134984382420159/250000000000000000)⟩,(78855198834731367/250000000000000000)⟩
theorem valid738 : certificate738.Valid := by decide +kernel
theorem sound738 : 0 ≤ cappedLabelEntropy (certificate738.rho:ℝ) ∧ cappedLabelEntropy (certificate738.rho:ℝ) ≤ (certificate738.bound:ℝ) := rat_label_entropy_certificate_sound certificate738 valid738

def certificate739 : RatLabelEntropyCertificate := ⟨(5099652283014399/1000000000000000000),⟨(1000000000000000000/5099652283014399),7,11,(5278582921377303489/1000000000000000000)⟩,⟨(1000000000000000000/994900347716985601),0,2,(5112699887451389/1000000000000000000)⟩,(16002782170940281/500000000000000000)⟩
theorem valid739 : certificate739.Valid := by decide +kernel
theorem sound739 : 0 ≤ cappedLabelEntropy (certificate739.rho:ℝ) ∧ cappedLabelEntropy (certificate739.rho:ℝ) ≤ (certificate739.bound:ℝ) := rat_label_entropy_certificate_sound certificate739 valid739

end Cycle12.CutLabelCertificates.Entropy036
