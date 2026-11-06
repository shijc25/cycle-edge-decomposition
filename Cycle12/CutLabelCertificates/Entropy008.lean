import Cycle12.RationalLabelEntropy
import Cycle12.RationalMinorityBudget

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CutLabelCertificates.Entropy008

def certificate160 : RatLabelEntropyCertificate := ⟨(192615164033101883/125000000000000000),⟨1,0,0,0⟩,⟨1,0,0,0⟩,(69314718055994531/100000000000000000)⟩
theorem valid160 : certificate160.Valid := by decide +kernel
theorem sound160 : 0 ≤ cappedLabelEntropy (certificate160.rho:ℝ) ∧ cappedLabelEntropy (certificate160.rho:ℝ) ≤ (certificate160.bound:ℝ) := rat_label_entropy_certificate_sound certificate160 valid160

def certificate161 : RatLabelEntropyCertificate := ⟨(1541343368582078201/1000000000000000000),⟨1,0,0,0⟩,⟨1,0,0,0⟩,(69314718055994531/100000000000000000)⟩
theorem valid161 : certificate161.Valid := by decide +kernel
theorem sound161 : 0 ≤ cappedLabelEntropy (certificate161.rho:ℝ) ∧ cappedLabelEntropy (certificate161.rho:ℝ) ≤ (certificate161.bound:ℝ) := rat_label_entropy_certificate_sound certificate161 valid161

def certificate162 : RatLabelEntropyCertificate := ⟨(771187030157534051/500000000000000000),⟨1,0,0,0⟩,⟨1,0,0,0⟩,(69314718055994531/100000000000000000)⟩
theorem valid162 : certificate162.Valid := by decide +kernel
theorem sound162 : 0 ≤ cappedLabelEntropy (certificate162.rho:ℝ) ∧ cappedLabelEntropy (certificate162.rho:ℝ) ≤ (certificate162.bound:ℝ) := rat_label_entropy_certificate_sound certificate162 valid162

def certificate163 : RatLabelEntropyCertificate := ⟨(77190396200158529/50000000000000000),⟨1,0,0,0⟩,⟨1,0,0,0⟩,(69314718055994531/100000000000000000)⟩
theorem valid163 : certificate163.Valid := by decide +kernel
theorem sound163 : 0 ≤ cappedLabelEntropy (certificate163.rho:ℝ) ∧ cappedLabelEntropy (certificate163.rho:ℝ) ≤ (certificate163.bound:ℝ) := rat_label_entropy_certificate_sound certificate163 valid163

def certificate164 : RatLabelEntropyCertificate := ⟨(193192031631279777/125000000000000000),⟨1,0,0,0⟩,⟨1,0,0,0⟩,(69314718055994531/100000000000000000)⟩
theorem valid164 : certificate164.Valid := by decide +kernel
theorem sound164 : 0 ≤ cappedLabelEntropy (certificate164.rho:ℝ) ∧ cappedLabelEntropy (certificate164.rho:ℝ) ≤ (certificate164.bound:ℝ) := rat_label_entropy_certificate_sound certificate164 valid164

def certificate165 : RatLabelEntropyCertificate := ⟨(30926889169404861/20000000000000000),⟨1,0,0,0⟩,⟨1,0,0,0⟩,(69314718055994531/100000000000000000)⟩
theorem valid165 : certificate165.Valid := by decide +kernel
theorem sound165 : 0 ≤ cappedLabelEntropy (certificate165.rho:ℝ) ∧ cappedLabelEntropy (certificate165.rho:ℝ) ≤ (certificate165.bound:ℝ) := rat_label_entropy_certificate_sound certificate165 valid165

def certificate166 : RatLabelEntropyCertificate := ⟨(777802003310447887/500000000000000000),⟨1,0,0,0⟩,⟨1,0,0,0⟩,(69314718055994531/100000000000000000)⟩
theorem valid166 : certificate166.Valid := by decide +kernel
theorem sound166 : 0 ≤ cappedLabelEntropy (certificate166.rho:ℝ) ∧ cappedLabelEntropy (certificate166.rho:ℝ) ≤ (certificate166.bound:ℝ) := rat_label_entropy_certificate_sound certificate166 valid166

def certificate167 : RatLabelEntropyCertificate := ⟨(97511076965477787/62500000000000000),⟨1,0,0,0⟩,⟨1,0,0,0⟩,(69314718055994531/100000000000000000)⟩
theorem valid167 : certificate167.Valid := by decide +kernel
theorem sound167 : 0 ≤ cappedLabelEntropy (certificate167.rho:ℝ) ∧ cappedLabelEntropy (certificate167.rho:ℝ) ≤ (certificate167.bound:ℝ) := rat_label_entropy_certificate_sound certificate167 valid167

def certificate168 : RatLabelEntropyCertificate := ⟨(1209342291522181/1000000000000000000),⟨(1000000000000000000/1209342291522181),9,12,(167941965697041093/25000000000000000)⟩,⟨(1000000000000000000/998790657708477819),0,2,(121007413600437/100000000000000000)⟩,(9332583607727791/1000000000000000000)⟩
theorem valid168 : certificate168.Valid := by decide +kernel
theorem sound168 : 0 ≤ cappedLabelEntropy (certificate168.rho:ℝ) ∧ cappedLabelEntropy (certificate168.rho:ℝ) ≤ (certificate168.bound:ℝ) := rat_label_entropy_certificate_sound certificate168 valid168

def certificate169 : RatLabelEntropyCertificate := ⟨(59313824402313/31250000000000000),⟨(31250000000000000/59313824402313),9,4,(195841632806752437/31250000000000000)⟩,⟨(31250000000000000/31190686175597687),0,2,(949922972918487/500000000000000000)⟩,(13791142965931707/1000000000000000000)⟩
theorem valid169 : certificate169.Valid := by decide +kernel
theorem sound169 : 0 ≤ cappedLabelEntropy (certificate169.rho:ℝ) ∧ cappedLabelEntropy (certificate169.rho:ℝ) ≤ (certificate169.bound:ℝ) := rat_label_entropy_certificate_sound certificate169 valid169

def certificate170 : RatLabelEntropyCertificate := ⟨(339456345882849/125000000000000000),⟨(125000000000000000/339456345882849),8,10,(2954361830554467263/500000000000000000)⟩,⟨(125000000000000000/124660543654117151),0,2,(339918104498777/125000000000000000)⟩,(9378994993876499/500000000000000000)⟩
theorem valid170 : certificate170.Valid := by decide +kernel
theorem sound170 : 0 ≤ cappedLabelEntropy (certificate170.rho:ℝ) ∧ cappedLabelEntropy (certificate170.rho:ℝ) ≤ (certificate170.bound:ℝ) := rat_label_entropy_certificate_sound certificate170 valid170

def certificate171 : RatLabelEntropyCertificate := ⟨(231356890103859/62500000000000000),⟨(62500000000000000/231356890103859),8,5,(1399740084662505893/250000000000000000)⟩,⟨(62500000000000000/62268643109896141),0,2,(29668628206847/8000000000000000)⟩,(24420579270983407/1000000000000000000)⟩
theorem valid171 : certificate171.Valid := by decide +kernel
theorem sound171 : 0 ≤ cappedLabelEntropy (certificate171.rho:ℝ) ∧ cappedLabelEntropy (certificate171.rho:ℝ) ≤ (certificate171.bound:ℝ) := rat_label_entropy_certificate_sound certificate171 valid171

def certificate172 : RatLabelEntropyCertificate := ⟨(484379359859359/100000000000000000),⟨(100000000000000000/484379359859359),7,13,(333128566493947423/62500000000000000)⟩,⟨(100000000000000000/99515620640140641),0,2,(60694534840007/12500000000000000)⟩,(6129947945905403/200000000000000000)⟩
theorem valid172 : certificate172.Valid := by decide +kernel
theorem sound172 : 0 ≤ cappedLabelEntropy (certificate172.rho:ℝ) ∧ cappedLabelEntropy (certificate172.rho:ℝ) ≤ (certificate172.bound:ℝ) := rat_label_entropy_certificate_sound certificate172 valid172

def certificate173 : RatLabelEntropyCertificate := ⟨(3071252082605993/500000000000000000),⟨(500000000000000000/3071252082605993),7,8,(2546261387735990207/500000000000000000)⟩,⟨(500000000000000000/496928747917394007),0,2,(770180869316731/125000000000000000)⟩,(7480888520145087/200000000000000000)⟩
theorem valid173 : certificate173.Valid := by decide +kernel
theorem sound173 : 0 ≤ cappedLabelEntropy (certificate173.rho:ℝ) ∧ cappedLabelEntropy (certificate173.rho:ℝ) ≤ (certificate173.bound:ℝ) := rat_label_entropy_certificate_sound certificate173 valid173

def certificate174 : RatLabelEntropyCertificate := ⟨(3769470964153143/500000000000000000),⟨(500000000000000000/3769470964153143),7,4,(4887673434619978199/1000000000000000000)⟩,⟨(500000000000000000/496230529035846857),0,3,(7567503390356219/1000000000000000000)⟩,(44358338609879409/1000000000000000000)⟩
theorem valid174 : certificate174.Valid := by decide +kernel
theorem sound174 : 0 ≤ cappedLabelEntropy (certificate174.rho:ℝ) ∧ cappedLabelEntropy (certificate174.rho:ℝ) ≤ (certificate174.bound:ℝ) := rat_label_entropy_certificate_sound certificate174 valid174

def certificate175 : RatLabelEntropyCertificate := ⟨(2285812250937881/250000000000000000),⟨(250000000000000000/2285812250937881),6,13,(29342121786318187/6250000000000000)⟩,⟨(250000000000000000/247714187749062119),0,3,(9185305053831959/1000000000000000000)⟩,(52026493649062901/1000000000000000000)⟩
theorem valid175 : certificate175.Valid := by decide +kernel
theorem sound175 : 0 ≤ cappedLabelEntropy (certificate175.rho:ℝ) ∧ cappedLabelEntropy (certificate175.rho:ℝ) ≤ (certificate175.bound:ℝ) := rat_label_entropy_certificate_sound certificate175 valid175

def certificate176 : RatLabelEntropyCertificate := ⟨(1354169940615399/125000000000000000),⟨(125000000000000000/1354169940615399),6,10,(565640632579032477/125000000000000000)⟩,⟨(125000000000000000/123645830059384601),0,3,(10892467644863613/1000000000000000000)⟩,(59796772303822341/1000000000000000000)⟩
theorem valid176 : certificate176.Valid := by decide +kernel
theorem sound176 : 0 ≤ cappedLabelEntropy (certificate176.rho:ℝ) ∧ cappedLabelEntropy (certificate176.rho:ℝ) ≤ (certificate176.bound:ℝ) := rat_label_entropy_certificate_sound certificate176 valid176

def certificate177 : RatLabelEntropyCertificate := ⟨(2549212559213693/200000000000000000),⟨(200000000000000000/2549212559213693),6,7,(4362532855374690569/1000000000000000000)⟩,⟨(200000000000000000/197450787440786307),0,3,(3206997692935303/250000000000000000)⟩,(13653920424066977/200000000000000000)⟩
theorem valid177 : certificate177.Valid := by decide +kernel
theorem sound177 : 0 ≤ cappedLabelEntropy (certificate177.rho:ℝ) ∧ cappedLabelEntropy (certificate177.rho:ℝ) ≤ (certificate177.bound:ℝ) := rat_label_entropy_certificate_sound certificate177 valid177

def certificate178 : RatLabelEntropyCertificate := ⟨(7351096944928787/500000000000000000),⟨(500000000000000000/7351096944928787),6,5,(2109879276062628529/500000000000000000)⟩,⟨(500000000000000000/492648903055071213),0,3,(3702835569344039/250000000000000000)⟩,(3065331658127013/40000000000000000)⟩
theorem valid178 : certificate178.Valid := by decide +kernel
theorem sound178 : 0 ≤ cappedLabelEntropy (certificate178.rho:ℝ) ∧ cappedLabelEntropy (certificate178.rho:ℝ) ≤ (certificate178.bound:ℝ) := rat_label_entropy_certificate_sound certificate178 valid178

def certificate179 : RatLabelEntropyCertificate := ⟨(676966562739121/40000000000000000),⟨(40000000000000000/676966562739121),5,14,(815802570348914783/200000000000000000)⟩,⟨(40000000000000000/39323033437260879),0,3,(17069014372713627/1000000000000000000)⟩,(21453504578334553/250000000000000000)⟩
theorem valid179 : certificate179.Valid := by decide +kernel
theorem sound179 : 0 ≤ cappedLabelEntropy (certificate179.rho:ℝ) ∧ cappedLabelEntropy (certificate179.rho:ℝ) ≤ (certificate179.bound:ℝ) := rat_label_entropy_certificate_sound certificate179 valid179

end Cycle12.CutLabelCertificates.Entropy008
