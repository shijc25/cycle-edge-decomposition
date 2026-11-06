import Cycle12.RationalLabelEntropy
import Cycle12.RationalMinorityBudget

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CutLabelCertificates.Entropy012

def certificate240 : RatLabelEntropyCertificate := ⟨(64547303303188991/200000000000000000),⟨(200000000000000000/64547303303188991),1,11,(70682439187236119/62500000000000000)⟩,⟨(200000000000000000/135452696696811009),0,10,(194847444523538741/500000000000000000)⟩,(314457492643087649/500000000000000000)⟩
theorem valid240 : certificate240.Valid := by decide +kernel
theorem sound240 : 0 ≤ cappedLabelEntropy (certificate240.rho:ℝ) ∧ cappedLabelEntropy (certificate240.rho:ℝ) ≤ (certificate240.bound:ℝ) := rat_label_entropy_certificate_sound certificate240 valid240

def certificate241 : RatLabelEntropyCertificate := ⟨(677063933453944777/500000000000000000),⟨1,0,0,0⟩,⟨1,0,0,0⟩,(69314718055994531/100000000000000000)⟩
theorem valid241 : certificate241.Valid := by decide +kernel
theorem sound241 : 0 ≤ cappedLabelEntropy (certificate241.rho:ℝ) ∧ cappedLabelEntropy (certificate241.rho:ℝ) ≤ (certificate241.bound:ℝ) := rat_label_entropy_certificate_sound certificate241 valid241

def certificate242 : RatLabelEntropyCertificate := ⟨(54224146449144577/40000000000000000),⟨1,0,0,0⟩,⟨1,0,0,0⟩,(69314718055994531/100000000000000000)⟩
theorem valid242 : certificate242.Valid := by decide +kernel
theorem sound242 : 0 ≤ cappedLabelEntropy (certificate242.rho:ℝ) ∧ cappedLabelEntropy (certificate242.rho:ℝ) ≤ (certificate242.bound:ℝ) := rat_label_entropy_certificate_sound certificate242 valid242

def certificate243 : RatLabelEntropyCertificate := ⟨(121862068682651/250000000000000000),⟨(250000000000000000/121862068682651),11,2,(1525265275254483173/200000000000000000)⟩,⟨(250000000000000000/249878137931317349),0,1,(243783558130921/500000000000000000)⟩,(2102384543579347/500000000000000000)⟩
theorem valid243 : certificate243.Valid := by decide +kernel
theorem sound243 : 0 ≤ cappedLabelEntropy (certificate243.rho:ℝ) ∧ cappedLabelEntropy (certificate243.rho:ℝ) ≤ (certificate243.bound:ℝ) := rat_label_entropy_certificate_sound certificate243 valid243

def certificate244 : RatLabelEntropyCertificate := ⟨(765758354021977/1000000000000000000),⟨(1000000000000000000/765758354021977),10,8,(1793660975679103381/250000000000000000)⟩,⟨(1000000000000000000/999234241645978023),0,2,(23939115522281/31250000000000000)⟩,(1564877147966139/250000000000000000)⟩
theorem valid244 : certificate244.Valid := by decide +kernel
theorem sound244 : 0 ≤ cappedLabelEntropy (certificate244.rho:ℝ) ∧ cappedLabelEntropy (certificate244.rho:ℝ) ≤ (certificate244.bound:ℝ) := rat_label_entropy_certificate_sound certificate244 valid244

def certificate245 : RatLabelEntropyCertificate := ⟨(1102230101737683/1000000000000000000),⟨(1000000000000000000/1102230101737683),9,13,(42565123664332381/6250000000000000)⟩,⟨(1000000000000000000/998897769898262317),0,2,(275709501019041/250000000000000000)⟩,(4304136058376497/500000000000000000)⟩
theorem valid245 : certificate245.Valid := by decide +kernel
theorem sound245 : 0 ≤ cappedLabelEntropy (certificate245.rho:ℝ) ∧ cappedLabelEntropy (certificate245.rho:ℝ) ≤ (certificate245.bound:ℝ) := rat_label_entropy_certificate_sound certificate245 valid245

def certificate246 : RatLabelEntropyCertificate := ⟨(23299860089729/15625000000000000),⟨(15625000000000000/23299860089729),9,9,(650818011878363679/100000000000000000)⟩,⟨(15625000000000000/15601700139910271),0,2,(746151988821881/500000000000000000)⟩,(2798754646131327/250000000000000000)⟩
theorem valid246 : certificate246.Valid := by decide +kernel
theorem sound246 : 0 ≤ cappedLabelEntropy (certificate246.rho:ℝ) ∧ cappedLabelEntropy (certificate246.rho:ℝ) ≤ (certificate246.bound:ℝ) := rat_label_entropy_certificate_sound certificate246 valid246

def certificate247 : RatLabelEntropyCertificate := ⟨(171374126462503/100000000000000000),⟨(100000000000000000/171374126462503),9,6,(1592269106082255969/250000000000000000)⟩,⟨(100000000000000000/99828625873537497),0,2,(1715211399046173/1000000000000000000)⟩,(6313610528208579/500000000000000000)⟩
theorem valid247 : certificate247.Valid := by decide +kernel
theorem sound247 : 0 ≤ cappedLabelEntropy (certificate247.rho:ℝ) ∧ cappedLabelEntropy (certificate247.rho:ℝ) ≤ (certificate247.bound:ℝ) := rat_label_entropy_certificate_sound certificate247 valid247

def certificate248 : RatLabelEntropyCertificate := ⟨(488055489124853/250000000000000000),⟨(250000000000000000/488055489124853),9,2,(6238787090232353159/1000000000000000000)⟩,⟨(250000000000000000/249511944510875147),0,2,(244266253187961/125000000000000000)⟩,(3532453067359681/250000000000000000)⟩
theorem valid248 : certificate248.Valid := by decide +kernel
theorem sound248 : 0 ≤ cappedLabelEntropy (certificate248.rho:ℝ) ∧ cappedLabelEntropy (certificate248.rho:ℝ) ≤ (certificate248.bound:ℝ) := rat_label_entropy_certificate_sound certificate248 valid248

def certificate249 : RatLabelEntropyCertificate := ⟨(2477389439905857/1000000000000000000),⟨(1000000000000000000/2477389439905857),8,11,(375034369901535069/62500000000000000)⟩,⟨(1000000000000000000/997522610560094143),0,2,(2480463246851711/1000000000000000000)⟩,(8670008587465423/500000000000000000)⟩
theorem valid249 : certificate249.Valid := by decide +kernel
theorem sound249 : 0 ≤ cappedLabelEntropy (certificate249.rho:ℝ) ∧ cappedLabelEntropy (certificate249.rho:ℝ) ≤ (certificate249.bound:ℝ) := rat_label_entropy_certificate_sound certificate249 valid249

def certificate250 : RatLabelEntropyCertificate := ⟨(766629854754553/250000000000000000),⟨(250000000000000000/766629854754553),8,8,(5787212100285574507/1000000000000000000)⟩,⟨(250000000000000000/249233370145245447),0,2,(1535615411950111/500000000000000000)⟩,(5202102780610333/250000000000000000)⟩
theorem valid250 : certificate250.Valid := by decide +kernel
theorem sound250 : 0 ≤ cappedLabelEntropy (certificate250.rho:ℝ) ∧ cappedLabelEntropy (certificate250.rho:ℝ) ≤ (certificate250.bound:ℝ) := rat_label_entropy_certificate_sound certificate250 valid250

def certificate251 : RatLabelEntropyCertificate := ⟨(58133147710997/15625000000000000),⟨(15625000000000000/58133147710997),8,4,(139847286121192671/25000000000000000)⟩,⟨(15625000000000000/15566866852289003),0,2,(931864952081273/250000000000000000)⟩,(24525784843268453/1000000000000000000)⟩
theorem valid251 : certificate251.Valid := by decide +kernel
theorem sound251 : 0 ≤ cappedLabelEntropy (certificate251.rho:ℝ) ∧ cappedLabelEntropy (certificate251.rho:ℝ) ≤ (certificate251.bound:ℝ) := rat_label_entropy_certificate_sound certificate251 valid251

def certificate252 : RatLabelEntropyCertificate := ⟨(4039312357072789/1000000000000000000),⟨(1000000000000000000/4039312357072789),7,15,(2755840405070781499/500000000000000000)⟩,⟨(1000000000000000000/995960687642927211),0,2,(80949848290681/20000000000000000)⟩,(26294543733054641/1000000000000000000)⟩
theorem valid252 : certificate252.Valid := by decide +kernel
theorem sound252 : 0 ≤ cappedLabelEntropy (certificate252.rho:ℝ) ∧ cappedLabelEntropy (certificate252.rho:ℝ) ≤ (certificate252.bound:ℝ) := rat_label_entropy_certificate_sound certificate252 valid252

def certificate253 : RatLabelEntropyCertificate := ⟨(176174374560843/40000000000000000),⟨(40000000000000000/176174374560843),7,14,(1356290115997733013/250000000000000000)⟩,⟨(40000000000000000/39823825625439157),0,2,(2207043564139693/500000000000000000)⟩,(14144501096598863/500000000000000000)⟩
theorem valid253 : certificate253.Valid := by decide +kernel
theorem sound253 : 0 ≤ cappedLabelEntropy (certificate253.rho:ℝ) ∧ cappedLabelEntropy (certificate253.rho:ℝ) ≤ (certificate253.bound:ℝ) := rat_label_entropy_certificate_sound certificate253 valid253

def certificate254 : RatLabelEntropyCertificate := ⟨(5184811632642599/1000000000000000000),⟨(1000000000000000000/5184811632642599),7,11,(2631010883624200717/500000000000000000)⟩,⟨(1000000000000000000/994815188367357401),0,2,(5198299409730627/1000000000000000000)⟩,(1298157555061167/40000000000000000)⟩
theorem valid254 : certificate254.Valid := by decide +kernel
theorem sound254 : 0 ≤ cappedLabelEntropy (certificate254.rho:ℝ) ∧ cappedLabelEntropy (certificate254.rho:ℝ) ≤ (certificate254.bound:ℝ) := rat_label_entropy_certificate_sound certificate254 valid254

def certificate255 : RatLabelEntropyCertificate := ⟨(1507745374617841/250000000000000000),⟨(250000000000000000/1507745374617841),7,9,(19964240282250463/3906250000000000)⟩,⟨(250000000000000000/248492254625382159),0,3,(3024620660419819/500000000000000000)⟩,(18418086592157959/500000000000000000)⟩
theorem valid255 : certificate255.Valid := by decide +kernel
theorem sound255 : 0 ≤ cappedLabelEntropy (certificate255.rho:ℝ) ∧ cappedLabelEntropy (certificate255.rho:ℝ) ≤ (certificate255.bound:ℝ) := rat_label_entropy_certificate_sound certificate255 valid255

def certificate256 : RatLabelEntropyCertificate := ⟨(861806645945301/125000000000000000),⟨(125000000000000000/861806645945301),7,6,(2488519039714917601/500000000000000000)⟩,⟨(125000000000000000/124138193354054699),0,3,(3459164858460681/500000000000000000)⟩,(10296146892123511/250000000000000000)⟩
theorem valid256 : certificate256.Valid := by decide +kernel
theorem sound256 : 0 ≤ cappedLabelEntropy (certificate256.rho:ℝ) ∧ cappedLabelEntropy (certificate256.rho:ℝ) ≤ (certificate256.bound:ℝ) := rat_label_entropy_certificate_sound certificate256 valid256

def certificate257 : RatLabelEntropyCertificate := ⟨(786365087049287/100000000000000000),⟨(100000000000000000/786365087049287),6,16,(2422752146520907051/500000000000000000)⟩,⟨(100000000000000000/99213634912950713),0,3,(315789296928511/40000000000000000)⟩,(4593600505567587/100000000000000000)⟩
theorem valid257 : certificate257.Valid := by decide +kernel
theorem sound257 : 0 ≤ cappedLabelEntropy (certificate257.rho:ℝ) ∧ cappedLabelEntropy (certificate257.rho:ℝ) ≤ (certificate257.bound:ℝ) := rat_label_entropy_certificate_sound certificate257 valid257

def certificate258 : RatLabelEntropyCertificate := ⟨(1783567945548239/200000000000000000),⟨(200000000000000000/1783567945548239),6,13,(4719701544709910057/1000000000000000000)⟩,⟨(200000000000000000/198216432054451761),0,3,(4478920829283613/500000000000000000)⟩,(25483749500422581/500000000000000000)⟩
theorem valid258 : certificate258.Valid := by decide +kernel
theorem sound258 : 0 ≤ cappedLabelEntropy (certificate258.rho:ℝ) ∧ cappedLabelEntropy (certificate258.rho:ℝ) ≤ (certificate258.bound:ℝ) := rat_label_entropy_certificate_sound certificate258 valid258

def certificate259 : RatLabelEntropyCertificate := ⟨(9950369523272171/1000000000000000000),⟨(1000000000000000000/9950369523272171),6,11,(1152536397620982781/250000000000000000)⟩,⟨(1000000000000000000/990049630476727829),0,3,(1000020531538329/100000000000000000)⟩,(55773351758585531/1000000000000000000)⟩
theorem valid259 : certificate259.Valid := by decide +kernel
theorem sound259 : 0 ≤ cappedLabelEntropy (certificate259.rho:ℝ) ∧ cappedLabelEntropy (certificate259.rho:ℝ) ≤ (certificate259.bound:ℝ) := rat_label_entropy_certificate_sound certificate259 valid259

end Cycle12.CutLabelCertificates.Entropy012
