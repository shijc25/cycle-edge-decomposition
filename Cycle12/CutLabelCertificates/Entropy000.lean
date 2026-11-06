import Cycle12.RationalLabelEntropy
import Cycle12.RationalMinorityBudget

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CutLabelCertificates.Entropy000

def certificate0 : RatLabelEntropyCertificate := ⟨(682378239891701/500000000000000000),⟨(500000000000000000/682378239891701),9,10,(131935585387000417/20000000000000000)⟩,⟨(500000000000000000/499317621760108299),0,2,(170711076011239/125000000000000000)⟩,(10366822029258913/1000000000000000000)⟩
theorem valid0 : certificate0.Valid := by decide +kernel
theorem sound0 : 0 ≤ cappedLabelEntropy (certificate0.rho:ℝ) ∧ cappedLabelEntropy (certificate0.rho:ℝ) ≤ (certificate0.bound:ℝ) := rat_label_entropy_certificate_sound certificate0 valid0

def certificate1 : RatLabelEntropyCertificate := ⟨1,⟨1,0,0,0⟩,⟨1,0,0,0⟩,(69314718055994531/100000000000000000)⟩
theorem valid1 : certificate1.Valid := by decide +kernel
theorem sound1 : 0 ≤ cappedLabelEntropy (certificate1.rho:ℝ) ∧ cappedLabelEntropy (certificate1.rho:ℝ) ≤ (certificate1.bound:ℝ) := rat_label_entropy_certificate_sound certificate1 valid1

def certificate2 : RatLabelEntropyCertificate := ⟨(172008488548027/250000000000000000),⟨(250000000000000000/172008488548027),10,10,(3640836184612644347/500000000000000000)⟩,⟨(250000000000000000/249827991511451973),0,2,(137654151635771/200000000000000000)⟩,(2848917518928521/500000000000000000)⟩
theorem valid2 : certificate2.Valid := by decide +kernel
theorem sound2 : 0 ≤ cappedLabelEntropy (certificate2.rho:ℝ) ∧ cappedLabelEntropy (certificate2.rho:ℝ) ≤ (certificate2.bound:ℝ) := rat_label_entropy_certificate_sound certificate2 valid2

def certificate3 : RatLabelEntropyCertificate := ⟨(60293605624453/25000000000000000),⟨(25000000000000000/60293605624453),8,12,(602740504845234619/100000000000000000)⟩,⟨(25000000000000000/24939706394375547),0,2,(1207328582267039/500000000000000000)⟩,(16945392946271123/1000000000000000000)⟩
theorem valid3 : certificate3.Valid := by decide +kernel
theorem sound3 : 0 ≤ cappedLabelEntropy (certificate3.rho:ℝ) ∧ cappedLabelEntropy (certificate3.rho:ℝ) ≤ (certificate3.bound:ℝ) := rat_label_entropy_certificate_sound certificate3 valid3

def certificate4 : RatLabelEntropyCertificate := ⟨(3768010709861431/1000000000000000000),⟨(1000000000000000000/3768010709861431),8,4,(44649664639617177/8000000000000000)⟩,⟨(1000000000000000000/996231989290138569),0,2,(1887563772691381/500000000000000000)⟩,(3098869330448189/125000000000000000)⟩
theorem valid4 : certificate4.Valid := by decide +kernel
theorem sound4 : 0 ≤ cappedLabelEntropy (certificate4.rho:ℝ) ∧ cappedLabelEntropy (certificate4.rho:ℝ) ≤ (certificate4.bound:ℝ) := rat_label_entropy_certificate_sound certificate4 valid4

def certificate5 : RatLabelEntropyCertificate := ⟨(2697171401962649/500000000000000000),⟨(500000000000000000/2697171401962649),7,10,(5222404503461358013/1000000000000000000)⟩,⟨(500000000000000000/497302828598037351),0,3,(5408944806882001/1000000000000000000)⟩,(16775603628410007/500000000000000000)⟩
theorem valid5 : certificate5.Valid := by decide +kernel
theorem sound5 : 0 ≤ cappedLabelEntropy (certificate5.rho:ℝ) ∧ cappedLabelEntropy (certificate5.rho:ℝ) ≤ (certificate5.bound:ℝ) := rat_label_entropy_certificate_sound certificate5 valid5

def certificate6 : RatLabelEntropyCertificate := ⟨(229686272577979/31250000000000000),⟨(31250000000000000/229686272577979),7,5,(4913060309649856979/1000000000000000000)⟩,⟨(31250000000000000/31020313727422021),0,3,(1475420954143607/200000000000000000)⟩,(10858420910896177/250000000000000000)⟩
theorem valid6 : certificate6.Valid := by decide +kernel
theorem sound6 : 0 ≤ cappedLabelEntropy (certificate6.rho:ℝ) ∧ cappedLabelEntropy (certificate6.rho:ℝ) ≤ (certificate6.bound:ℝ) := rat_label_entropy_certificate_sound certificate6 valid6

def certificate7 : RatLabelEntropyCertificate := ⟨(4767698567625307/500000000000000000),⟨(500000000000000000/4767698567625307),6,12,(930548878106969287/200000000000000000)⟩,⟨(500000000000000000/495232301432374693),0,3,(2395287528841693/250000000000000000)⟩,(53855555576563637/1000000000000000000)⟩
theorem valid7 : certificate7.Valid := by decide +kernel
theorem sound7 : 0 ≤ cappedLabelEntropy (certificate7.rho:ℝ) ∧ cappedLabelEntropy (certificate7.rho:ℝ) ≤ (certificate7.bound:ℝ) := rat_label_entropy_certificate_sound certificate7 valid7

def certificate8 : RatLabelEntropyCertificate := ⟨(12086903197871829/1000000000000000000),⟨(1000000000000000000/12086903197871829),6,8,(551954099114655533/125000000000000000)⟩,⟨(1000000000000000000/987913096802128171),0,3,(12160543805162167/1000000000000000000)⟩,(1021638853354607/15625000000000000)⟩
theorem valid8 : certificate8.Valid := by decide +kernel
theorem sound8 : 0 ≤ cappedLabelEntropy (certificate8.rho:ℝ) ∧ cappedLabelEntropy (certificate8.rho:ℝ) ≤ (certificate8.bound:ℝ) := rat_label_entropy_certificate_sound certificate8 valid8

def certificate9 : RatLabelEntropyCertificate := ⟨(23752993401881/1600000000000000),⟨(1600000000000000/23752993401881),6,5,(4210050347715403653/1000000000000000000)⟩,⟨(1600000000000000/1576247006598119),0,3,(233701875249603/15625000000000000)⟩,(77235686583736397/1000000000000000000)⟩
theorem valid9 : certificate9.Valid := by decide +kernel
theorem sound9 : 0 ≤ cappedLabelEntropy (certificate9.rho:ℝ) ∧ cappedLabelEntropy (certificate9.rho:ℝ) ≤ (certificate9.bound:ℝ) := rat_label_entropy_certificate_sound certificate9 valid9

def certificate10 : RatLabelEntropyCertificate := ⟨(17998956320876493/1000000000000000000),⟨(1000000000000000000/17998956320876493),5,13,(4017441504940531731/1000000000000000000)⟩,⟨(1000000000000000000/982001043679123507),0,3,(9081453909268937/500000000000000000)⟩,(90145748603152859/1000000000000000000)⟩
theorem valid10 : certificate10.Valid := by decide +kernel
theorem sound10 : 0 ≤ cappedLabelEntropy (certificate10.rho:ℝ) ∧ cappedLabelEntropy (certificate10.rho:ℝ) ≤ (certificate10.bound:ℝ) := rat_label_entropy_certificate_sound certificate10 valid10

def certificate11 : RatLabelEntropyCertificate := ⟨(10643909018980193/500000000000000000),⟨(500000000000000000/10643909018980193),5,10,(1924810146488805043/500000000000000000)⟩,⟨(500000000000000000/489356090981019807),0,3,(21517671542878521/1000000000000000000)⟩,(103009623578620239/1000000000000000000)⟩
theorem valid11 : certificate11.Valid := by decide +kernel
theorem sound11 : 0 ≤ cappedLabelEntropy (certificate11.rho:ℝ) ∧ cappedLabelEntropy (certificate11.rho:ℝ) ≤ (certificate11.bound:ℝ) := rat_label_entropy_certificate_sound certificate11 valid11

def certificate12 : RatLabelEntropyCertificate := ⟨(24864078235498561/1000000000000000000),⟨(1000000000000000000/24864078235498561),5,8,(3694331158264746167/1000000000000000000)⟩,⟨(1000000000000000000/975135921764501439),0,3,(25178410762583859/1000000000000000000)⟩,(2910212793361803/25000000000000000)⟩
theorem valid12 : certificate12.Valid := by decide +kernel
theorem sound12 : 0 ≤ cappedLabelEntropy (certificate12.rho:ℝ) ∧ cappedLabelEntropy (certificate12.rho:ℝ) ≤ (certificate12.bound:ℝ) := rat_label_entropy_certificate_sound certificate12 valid12

def certificate13 : RatLabelEntropyCertificate := ⟨(28906929096128577/1000000000000000000),⟨(1000000000000000000/28906929096128577),5,5,(3543673951490137027/1000000000000000000)⟩,⟨(1000000000000000000/971093070903871423),0,4,(14666482356885569/500000000000000000)⟩,(32730442609533521/250000000000000000)⟩
theorem valid13 : certificate13.Valid := by decide +kernel
theorem sound13 : 0 ≤ cappedLabelEntropy (certificate13.rho:ℝ) ∧ cappedLabelEntropy (certificate13.rho:ℝ) ≤ (certificate13.bound:ℝ) := rat_label_entropy_certificate_sound certificate13 valid13

def certificate14 : RatLabelEntropyCertificate := ⟨(32988514750136009/1000000000000000000),⟨(1000000000000000000/32988514750136009),4,14,(3411595815969560633/1000000000000000000)⟩,⟨(1000000000000000000/967011485249863991),0,4,(3354490640199863/100000000000000000)⟩,(144981788658978511/1000000000000000000)⟩
theorem valid14 : certificate14.Valid := by decide +kernel
theorem sound14 : 0 ≤ cappedLabelEntropy (certificate14.rho:ℝ) ∧ cappedLabelEntropy (certificate14.rho:ℝ) ≤ (certificate14.bound:ℝ) := rat_label_entropy_certificate_sound certificate14 valid14

def certificate15 : RatLabelEntropyCertificate := ⟨(1868390842057391/50000000000000000),⟨(50000000000000000/1868390842057391),4,13,(821736364320910741/250000000000000000)⟩,⟨(50000000000000000/48131609157942609),0,4,(1904194454873879/50000000000000000)⟩,(19935844139962811/125000000000000000)⟩
theorem valid15 : certificate15.Valid := by decide +kernel
theorem sound15 : 0 ≤ cappedLabelEntropy (certificate15.rho:ℝ) ∧ cappedLabelEntropy (certificate15.rho:ℝ) ≤ (certificate15.bound:ℝ) := rat_label_entropy_certificate_sound certificate15 valid15

def certificate16 : RatLabelEntropyCertificate := ⟨(5248030969926309/125000000000000000),⟨(125000000000000000/5248030969926309),4,10,(792615196099058931/250000000000000000)⟩,⟨(125000000000000000/119751969030073691),0,4,(4289105830659471/100000000000000000)⟩,(34839944114314749/200000000000000000)⟩
theorem valid16 : certificate16.Valid := by decide +kernel
theorem sound16 : 0 ≤ cappedLabelEntropy (certificate16.rho:ℝ) ∧ cappedLabelEntropy (certificate16.rho:ℝ) ≤ (certificate16.bound:ℝ) := rat_label_entropy_certificate_sound certificate16 valid16

def certificate17 : RatLabelEntropyCertificate := ⟨(11804117289452677/250000000000000000),⟨(250000000000000000/11804117289452677),4,9,(1526506262207535349/500000000000000000)⟩,⟨(250000000000000000/238195882710547323),0,4,(48367546100730929/1000000000000000000)⟩,(190236273049480777/1000000000000000000)⟩
theorem valid17 : certificate17.Valid := by decide +kernel
theorem sound17 : 0 ≤ cappedLabelEntropy (certificate17.rho:ℝ) ∧ cappedLabelEntropy (certificate17.rho:ℝ) ≤ (certificate17.bound:ℝ) := rat_label_entropy_certificate_sound certificate17 valid17

def certificate18 : RatLabelEntropyCertificate := ⟨(52322619793003051/1000000000000000000),⟨(1000000000000000000/52322619793003051),4,7,(29503265005905437/10000000000000000)⟩,⟨(1000000000000000000/947677380206996949),0,4,(26870575442586109/500000000000000000)⟩,(205298084835789153/1000000000000000000)⟩
theorem valid18 : certificate18.Valid := by decide +kernel
theorem sound18 : 0 ≤ cappedLabelEntropy (certificate18.rho:ℝ) ∧ cappedLabelEntropy (certificate18.rho:ℝ) ≤ (certificate18.bound:ℝ) := rat_label_entropy_certificate_sound certificate18 valid18

def certificate19 : RatLabelEntropyCertificate := ⟨(57721365009697971/1000000000000000000),⟨(1000000000000000000/57721365009697971),4,5,(1426063948269714811/500000000000000000)⟩,⟨(1000000000000000000/942278634990302029),0,5,(5945425728307269/100000000000000000)⟩,(110325595883775233/500000000000000000)⟩
theorem valid19 : certificate19.Valid := by decide +kernel
theorem sound19 : 0 ≤ cappedLabelEntropy (certificate19.rho:ℝ) ∧ cappedLabelEntropy (certificate19.rho:ℝ) ≤ (certificate19.bound:ℝ) := rat_label_entropy_certificate_sound certificate19 valid19

end Cycle12.CutLabelCertificates.Entropy000
