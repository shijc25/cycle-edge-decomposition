import Cycle12.RationalLabelEntropy
import Cycle12.RationalMinorityBudget

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CutLabelCertificates.Entropy029

def certificate580 : RatLabelEntropyCertificate := ⟨(9914456536980941/1000000000000000000),⟨(1000000000000000000/9914456536980941),6,12,(92275226614365511/20000000000000000)⟩,⟨(1000000000000000000/990085543463019059),0,3,(1992786409602933/200000000000000000)⟩,(11121616252439377/200000000000000000)⟩
theorem valid580 : certificate580.Valid := by decide +kernel
theorem sound580 : 0 ≤ cappedLabelEntropy (certificate580.rho:ℝ) ∧ cappedLabelEntropy (certificate580.rho:ℝ) ≤ (certificate580.bound:ℝ) := rat_label_entropy_certificate_sound certificate580 valid580

def certificate581 : RatLabelEntropyCertificate := ⟨(9584407651009827/100000000000000000),⟨(100000000000000000/9584407651009827),3,9,(5862581527454531/2500000000000000)⟩,⟨(100000000000000000/90415592348990173),0,6,(100753451726608111/1000000000000000000)⟩,(315854315176282931/1000000000000000000)⟩
theorem valid581 : certificate581.Valid := by decide +kernel
theorem sound581 : 0 ≤ cappedLabelEntropy (certificate581.rho:ℝ) ∧ cappedLabelEntropy (certificate581.rho:ℝ) ≤ (certificate581.bound:ℝ) := rat_label_entropy_certificate_sound certificate581 valid581

def certificate582 : RatLabelEntropyCertificate := ⟨(465364246176779/200000000000000000),⟨(200000000000000000/465364246176779),8,12,(6063252221470458201/1000000000000000000)⟩,⟨(200000000000000000/199534635753823221),0,2,(2329532485957901/1000000000000000000)⟩,(16432216077432943/1000000000000000000)⟩
theorem valid582 : certificate582.Valid := by decide +kernel
theorem sound582 : 0 ≤ cappedLabelEntropy (certificate582.rho:ℝ) ∧ cappedLabelEntropy (certificate582.rho:ℝ) ≤ (certificate582.bound:ℝ) := rat_label_entropy_certificate_sound certificate582 valid582

def certificate583 : RatLabelEntropyCertificate := ⟨(1879069841860299/1000000000000000000),⟨(1000000000000000000/1879069841860299),9,4,(6276978389544778573/1000000000000000000)⟩,⟨(1000000000000000000/998120930158139701),0,2,(1880837508321849/1000000000000000000)⟩,(854511504567809/62500000000000000)⟩
theorem valid583 : certificate583.Valid := by decide +kernel
theorem sound583 : 0 ≤ cappedLabelEntropy (certificate583.rho:ℝ) ∧ cappedLabelEntropy (certificate583.rho:ℝ) ≤ (certificate583.bound:ℝ) := rat_label_entropy_certificate_sound certificate583 valid583

def certificate584 : RatLabelEntropyCertificate := ⟨(2138279437563053/1000000000000000000),⟨(1000000000000000000/2138279437563053),8,14,(3073876887234698769/500000000000000000)⟩,⟨(1000000000000000000/997861720562436947),0,2,(535142205295771/250000000000000000)⟩,(764080358501831/50000000000000000)⟩
theorem valid584 : certificate584.Valid := by decide +kernel
theorem sound584 : 0 ≤ cappedLabelEntropy (certificate584.rho:ℝ) ∧ cappedLabelEntropy (certificate584.rho:ℝ) ≤ (certificate584.bound:ℝ) := rat_label_entropy_certificate_sound certificate584 valid584

def certificate585 : RatLabelEntropyCertificate := ⟨(645272153956361/62500000000000000),⟨(62500000000000000/645272153956361),6,11,(4573249663803718141/1000000000000000000)⟩,⟨(62500000000000000/61854727846043639),0,3,(5189010153600057/500000000000000000)⟩,(114973449050413/2000000000000000)⟩
theorem valid585 : certificate585.Valid := by decide +kernel
theorem sound585 : 0 ≤ cappedLabelEntropy (certificate585.rho:ℝ) ∧ cappedLabelEntropy (certificate585.rho:ℝ) ≤ (certificate585.bound:ℝ) := rat_label_entropy_certificate_sound certificate585 valid585

def certificate586 : RatLabelEntropyCertificate := ⟨(23919908503919399/250000000000000000),⟨(250000000000000000/23919908503919399),3,8,(1173374906937056379/500000000000000000)⟩,⟨(250000000000000000/226080091496080601),0,5,(100571594219455847/1000000000000000000)⟩,(157742552104999851/500000000000000000)⟩
theorem valid586 : certificate586.Valid := by decide +kernel
theorem sound586 : 0 ≤ cappedLabelEntropy (certificate586.rho:ℝ) ∧ cappedLabelEntropy (certificate586.rho:ℝ) ≤ (certificate586.bound:ℝ) := rat_label_entropy_certificate_sound certificate586 valid586

def certificate587 : RatLabelEntropyCertificate := ⟨(239503584267541/100000000000000000),⟨(100000000000000000/239503584267541),8,12,(3017178541302383187/500000000000000000)⟩,⟨(100000000000000000/99760496415732459),0,2,(2397908528726597/1000000000000000000)⟩,(4211166738048369/250000000000000000)⟩
theorem valid587 : certificate587.Valid := by decide +kernel
theorem sound587 : 0 ≤ cappedLabelEntropy (certificate587.rho:ℝ) ∧ cappedLabelEntropy (certificate587.rho:ℝ) ≤ (certificate587.bound:ℝ) := rat_label_entropy_certificate_sound certificate587 valid587

def certificate588 : RatLabelEntropyCertificate := ⟨(241570038100673/125000000000000000),⟨(125000000000000000/241570038100673),9,3,(1249781914479635921/200000000000000000)⟩,⟨(125000000000000000/124758429961899327),0,2,(241803763608209/125000000000000000)⟩,(7003543146979983/500000000000000000)⟩
theorem valid588 : certificate588.Valid := by decide +kernel
theorem sound588 : 0 ≤ cappedLabelEntropy (certificate588.rho:ℝ) ∧ cappedLabelEntropy (certificate588.rho:ℝ) ≤ (certificate588.bound:ℝ) := rat_label_entropy_certificate_sound certificate588 valid588

def certificate589 : RatLabelEntropyCertificate := ⟨(2189842486291511/1000000000000000000),⟨(1000000000000000000/2189842486291511),8,13,(6123925661808190591/1000000000000000000)⟩,⟨(1000000000000000000/997810157513708489),0,2,(2192243697505577/1000000000000000000)⟩,(1559787562623491/100000000000000000)⟩
theorem valid589 : certificate589.Valid := by decide +kernel
theorem sound589 : 0 ≤ cappedLabelEntropy (certificate589.rho:ℝ) ∧ cappedLabelEntropy (certificate589.rho:ℝ) ≤ (certificate589.bound:ℝ) := rat_label_entropy_certificate_sound certificate589 valid589

def certificate590 : RatLabelEntropyCertificate := ⟨(5046179467089193/500000000000000000),⟨(500000000000000000/5046179467089193),6,12,(2297988341313534977/500000000000000000)⟩,⟨(500000000000000000/494953820532910807),0,3,(10143632058162443/1000000000000000000)⟩,(56425505216722079/1000000000000000000)⟩
theorem valid590 : certificate590.Valid := by decide +kernel
theorem sound590 : 0 ≤ cappedLabelEntropy (certificate590.rho:ℝ) ∧ cappedLabelEntropy (certificate590.rho:ℝ) ≤ (certificate590.bound:ℝ) := rat_label_entropy_certificate_sound certificate590 valid590

def certificate591 : RatLabelEntropyCertificate := ⟨(95588292312532843/1000000000000000000),⟨(1000000000000000000/95588292312532843),3,8,(2347704931774349591/1000000000000000000)⟩,⟨(1000000000000000000/904411707687467157),0,6,(50235296704194131/500000000000000000)⟩,(157639943119437557/500000000000000000)⟩
theorem valid591 : certificate591.Valid := by decide +kernel
theorem sound591 : 0 ≤ cappedLabelEntropy (certificate591.rho:ℝ) ∧ cappedLabelEntropy (certificate591.rho:ℝ) ≤ (certificate591.bound:ℝ) := rat_label_entropy_certificate_sound certificate591 valid591

def certificate592 : RatLabelEntropyCertificate := ⟨(2428542085296809/1000000000000000000),⟨(1000000000000000000/2428542085296809),8,12,(3010232083289535961/500000000000000000)⟩,⟨(1000000000000000000/997571457914703191),0,2,(2431495776705151/1000000000000000000)⟩,(1065408836777491/62500000000000000)⟩
theorem valid592 : certificate592.Valid := by decide +kernel
theorem sound592 : 0 ≤ cappedLabelEntropy (certificate592.rho:ℝ) ∧ cappedLabelEntropy (certificate592.rho:ℝ) ≤ (certificate592.bound:ℝ) := rat_label_entropy_certificate_sound certificate592 valid592

def certificate593 : RatLabelEntropyCertificate := ⟨(979216091562409/500000000000000000),⟨(500000000000000000/979216091562409),8,16,(1558902758101162609/250000000000000000)⟩,⟨(500000000000000000/499020783908437591),0,2,(980176209471723/500000000000000000)⟩,(14168534528985361/1000000000000000000)⟩
theorem valid593 : certificate593.Valid := by decide +kernel
theorem sound593 : 0 ≤ cappedLabelEntropy (certificate593.rho:ℝ) ∧ cappedLabelEntropy (certificate593.rho:ℝ) ≤ (certificate593.bound:ℝ) := rat_label_entropy_certificate_sound certificate593 valid593

def certificate594 : RatLabelEntropyCertificate := ⟨(110992440771977/50000000000000000),⟨(50000000000000000/110992440771977),8,13,(1222063237314059633/200000000000000000)⟩,⟨(50000000000000000/49889007559228023),0,2,(1111158166086813/500000000000000000)⟩,(15781361274615243/1000000000000000000)⟩
theorem valid594 : certificate594.Valid := by decide +kernel
theorem sound594 : 0 ≤ cappedLabelEntropy (certificate594.rho:ℝ) ∧ cappedLabelEntropy (certificate594.rho:ℝ) ≤ (certificate594.bound:ℝ) := rat_label_entropy_certificate_sound certificate594 valid594

def certificate595 : RatLabelEntropyCertificate := ⟨(2584945228113577/250000000000000000),⟨(250000000000000000/2584945228113577),6,11,(571469574809622181/125000000000000000)⟩,⟨(250000000000000000/247415054771886423),0,3,(81200060995787/7812500000000000)⟩,(57557101793160903/1000000000000000000)⟩
theorem valid595 : certificate595.Valid := by decide +kernel
theorem sound595 : 0 ≤ cappedLabelEntropy (certificate595.rho:ℝ) ∧ cappedLabelEntropy (certificate595.rho:ℝ) ≤ (certificate595.bound:ℝ) := rat_label_entropy_certificate_sound certificate595 valid595

def certificate596 : RatLabelEntropyCertificate := ⟨(95499891062040501/1000000000000000000),⟨(1000000000000000000/95499891062040501),3,8,(587157543051930223/250000000000000000)⟩,⟨(1000000000000000000/904500108937959499),0,5,(100372853706817147/1000000000000000000)⟩,(315081182703088749/1000000000000000000)⟩
theorem valid596 : certificate596.Valid := by decide +kernel
theorem sound596 : 0 ≤ cappedLabelEntropy (certificate596.rho:ℝ) ∧ cappedLabelEntropy (certificate596.rho:ℝ) ≤ (certificate596.bound:ℝ) := rat_label_entropy_certificate_sound certificate596 valid596

def certificate597 : RatLabelEntropyCertificate := ⟨(1231681982045001/500000000000000000),⟨(500000000000000000/1231681982045001),8,12,(3003113699044751163/500000000000000000)⟩,⟨(500000000000000000/498768318017954999),0,2,(2466403037020833/1000000000000000000)⟩,(17255851521242249/1000000000000000000)⟩
theorem valid597 : certificate597.Valid := by decide +kernel
theorem sound597 : 0 ≤ cappedLabelEntropy (certificate597.rho:ℝ) ∧ cappedLabelEntropy (certificate597.rho:ℝ) ≤ (certificate597.bound:ℝ) := rat_label_entropy_certificate_sound certificate597 valid597

def certificate598 : RatLabelEntropyCertificate := ⟨(99295691463951/50000000000000000),⟨(50000000000000000/99295691463951),8,15,(6221676103384568291/1000000000000000000)⟩,⟨(50000000000000000/49900704308536049),0,2,(1987888370760257/1000000000000000000)⟩,(7169826605379961/500000000000000000)⟩
theorem valid598 : certificate598.Valid := by decide +kernel
theorem sound598 : 0 ≤ cappedLabelEntropy (certificate598.rho:ℝ) ∧ cappedLabelEntropy (certificate598.rho:ℝ) ≤ (certificate598.bound:ℝ) := rat_label_entropy_certificate_sound certificate598 valid598

def certificate599 : RatLabelEntropyCertificate := ⟨(1125668730086787/500000000000000000),⟨(500000000000000000/1125668730086787),8,13,(1524057703155898373/250000000000000000)⟩,⟨(500000000000000000/498874331269913213),0,2,(1126937765218673/500000000000000000)⟩,(3993368522587247/250000000000000000)⟩
theorem valid599 : certificate599.Valid := by decide +kernel
theorem sound599 : 0 ≤ cappedLabelEntropy (certificate599.rho:ℝ) ∧ cappedLabelEntropy (certificate599.rho:ℝ) ≤ (certificate599.bound:ℝ) := rat_label_entropy_certificate_sound certificate599 valid599

end Cycle12.CutLabelCertificates.Entropy029
