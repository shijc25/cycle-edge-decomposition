import Cycle12.RationalLabelEntropy
import Cycle12.RationalMinorityBudget

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CutLabelCertificates.Entropy040

def certificate800 : RatLabelEntropyCertificate := ⟨(6077227058268507/1000000000000000000),⟨(1000000000000000000/6077227058268507),7,8,(1020641352596201363/200000000000000000)⟩,⟨(1000000000000000000/993922772941731493),0,2,(609576856141133/100000000000000000)⟩,(37072069415695993/1000000000000000000)⟩
theorem valid800 : certificate800.Valid := by decide +kernel
theorem sound800 : 0 ≤ cappedLabelEntropy (certificate800.rho:ℝ) ∧ cappedLabelEntropy (certificate800.rho:ℝ) ≤ (certificate800.bound:ℝ) := rat_label_entropy_certificate_sound certificate800 valid800

def certificate801 : RatLabelEntropyCertificate := ⟨(6411879328005419/1000000000000000000),⟨(1000000000000000000/6411879328005419),7,7,(5049602864124116457/1000000000000000000)⟩,⟨(1000000000000000000/993588120671994581),0,3,(1286504743962101/200000000000000000)⟩,(38768723373058927/1000000000000000000)⟩
theorem valid801 : certificate801.Valid := by decide +kernel
theorem sound801 : 0 ≤ cappedLabelEntropy (certificate801.rho:ℝ) ∧ cappedLabelEntropy (certificate801.rho:ℝ) ≤ (certificate801.bound:ℝ) := rat_label_entropy_certificate_sound certificate801 valid801

def certificate802 : RatLabelEntropyCertificate := ⟨(2264482568485693/200000000000000000),⟨(200000000000000000/2264482568485693),6,9,(448097108029561809/100000000000000000)⟩,⟨(200000000000000000/197735517431514307),0,3,(5693499669074143/500000000000000000)⟩,(61993475536694971/1000000000000000000)⟩
theorem valid802 : certificate802.Valid := by decide +kernel
theorem sound802 : 0 ≤ cappedLabelEntropy (certificate802.rho:ℝ) ∧ cappedLabelEntropy (certificate802.rho:ℝ) ≤ (certificate802.bound:ℝ) := rat_label_entropy_certificate_sound certificate802 valid802

def certificate803 : RatLabelEntropyCertificate := ⟨(3216433726645509/40000000000000000),⟨(40000000000000000/3216433726645509),3,12,(2520606246640247453/1000000000000000000)⟩,⟨(40000000000000000/36783566273354491),0,5,(2619633666855479/31250000000000000)⟩,(11190865938381093/40000000000000000)⟩
theorem valid803 : certificate803.Valid := by decide +kernel
theorem sound803 : 0 ≤ cappedLabelEntropy (certificate803.rho:ℝ) ∧ cappedLabelEntropy (certificate803.rho:ℝ) ≤ (certificate803.bound:ℝ) := rat_label_entropy_certificate_sound certificate803 valid803

def certificate804 : RatLabelEntropyCertificate := ⟨(47205818559660539/500000000000000000),⟨(500000000000000000/47205818559660539),3,8,(2360090938859288129/1000000000000000000)⟩,⟨(500000000000000000/452794181440339461),0,5,(19834084358342307/200000000000000000)⟩,(62525525840944671/200000000000000000)⟩
theorem valid804 : certificate804.Valid := by decide +kernel
theorem sound804 : 0 ≤ cappedLabelEntropy (certificate804.rho:ℝ) ∧ cappedLabelEntropy (certificate804.rho:ℝ) ≤ (certificate804.bound:ℝ) := rat_label_entropy_certificate_sound certificate804 valid804

def certificate805 : RatLabelEntropyCertificate := ⟨(1542608911993319/200000000000000000),⟨(200000000000000000/1542608911993319),7,3,(4864842284792121379/1000000000000000000)⟩,⟨(200000000000000000/198457391088006681),0,3,(3871471965419783/500000000000000000)⟩,(4520596757908701/100000000000000000)⟩
theorem valid805 : certificate805.Valid := by decide +kernel
theorem sound805 : 0 ≤ cappedLabelEntropy (certificate805.rho:ℝ) ∧ cappedLabelEntropy (certificate805.rho:ℝ) ≤ (certificate805.bound:ℝ) := rat_label_entropy_certificate_sound certificate805 valid805

def certificate806 : RatLabelEntropyCertificate := ⟨(6295695008995563/1000000000000000000),⟨(1000000000000000000/6295695008995563),7,8,(5067889211067776193/1000000000000000000)⟩,⟨(1000000000000000000/993704304991004437),0,2,(157889911745189/25000000000000000)⟩,(38181720212895623/1000000000000000000)⟩
theorem valid806 : certificate806.Valid := by decide +kernel
theorem sound806 : 0 ≤ cappedLabelEntropy (certificate806.rho:ℝ) ∧ cappedLabelEntropy (certificate806.rho:ℝ) ≤ (certificate806.bound:ℝ) := rat_label_entropy_certificate_sound certificate806 valid806

def certificate807 : RatLabelEntropyCertificate := ⟨(6644196927463109/1000000000000000000),⟨(1000000000000000000/6644196927463109),7,7,(5014011447775231901/1000000000000000000)⟩,⟨(1000000000000000000/993355803072536891),0,2,(6666367863814857/1000000000000000000)⟩,(39936154658509811/1000000000000000000)⟩
theorem valid807 : certificate807.Valid := by decide +kernel
theorem sound807 : 0 ≤ cappedLabelEntropy (certificate807.rho:ℝ) ∧ cappedLabelEntropy (certificate807.rho:ℝ) ≤ (certificate807.bound:ℝ) := rat_label_entropy_certificate_sound certificate807 valid807

def certificate808 : RatLabelEntropyCertificate := ⟨(367436056828811/31250000000000000),⟨(31250000000000000/367436056828811),6,9,(4443225346674189941/1000000000000000000)⟩,⟨(31250000000000000/30882563943171189),0,3,(11827625224800627/1000000000000000000)⟩,(1997868593284561/31250000000000000)⟩
theorem valid808 : certificate808.Valid := by decide +kernel
theorem sound808 : 0 ≤ cappedLabelEntropy (certificate808.rho:ℝ) ∧ cappedLabelEntropy (certificate808.rho:ℝ) ≤ (certificate808.bound:ℝ) := rat_label_entropy_certificate_sound certificate808 valid808

def certificate809 : RatLabelEntropyCertificate := ⟨(41455990174697343/500000000000000000),⟨(500000000000000000/41455990174697343),3,11,(2489975711608029571/1000000000000000000)⟩,⟨(500000000000000000/458544009825302657),0,5,(86551824799254457/1000000000000000000)⟩,(142912229436804709/500000000000000000)⟩
theorem valid809 : certificate809.Valid := by decide +kernel
theorem sound809 : 0 ≤ cappedLabelEntropy (certificate809.rho:ℝ) ∧ cappedLabelEntropy (certificate809.rho:ℝ) ≤ (certificate809.bound:ℝ) := rat_label_entropy_certificate_sound certificate809 valid809

def certificate810 : RatLabelEntropyCertificate := ⟨(94312794012477321/1000000000000000000),⟨(1000000000000000000/94312794012477321),3,9,(118056921251520413/50000000000000000)⟩,⟨(1000000000000000000/905687205987522679),0,6,(12382659975637739/125000000000000000)⟩,(19525255977691811/62500000000000000)⟩
theorem valid810 : certificate810.Valid := by decide +kernel
theorem sound810 : 0 ≤ cappedLabelEntropy (certificate810.rho:ℝ) ∧ cappedLabelEntropy (certificate810.rho:ℝ) ≤ (certificate810.bound:ℝ) := rat_label_entropy_certificate_sound certificate810 valid810

def certificate811 : RatLabelEntropyCertificate := ⟨(4005956938274481/500000000000000000),⟨(500000000000000000/4005956938274481),6,15,(2413412805271879037/500000000000000000)⟩,⟨(500000000000000000/495994043061725519),0,3,(8044181725582911/1000000000000000000)⟩,(46651843523187683/1000000000000000000)⟩
theorem valid811 : certificate811.Valid := by decide +kernel
theorem sound811 : 0 ≤ cappedLabelEntropy (certificate811.rho:ℝ) ∧ cappedLabelEntropy (certificate811.rho:ℝ) ≤ (certificate811.bound:ℝ) := rat_label_entropy_certificate_sound certificate811 valid811

def certificate812 : RatLabelEntropyCertificate := ⟨(6523524800421189/1000000000000000000),⟨(1000000000000000000/6523524800421189),7,7,(629042554445113637/125000000000000000)⟩,⟨(1000000000000000000/993476475199578811),0,3,(818111997832519/125000000000000000)⟩,(39330797826945051/1000000000000000000)⟩
theorem valid812 : certificate812.Valid := by decide +kernel
theorem sound812 : 0 ≤ cappedLabelEntropy (certificate812.rho:ℝ) ∧ cappedLabelEntropy (certificate812.rho:ℝ) ≤ (certificate812.bound:ℝ) := rat_label_entropy_certificate_sound certificate812 valid812

def certificate813 : RatLabelEntropyCertificate := ⟨(6886350524917807/1000000000000000000),⟨(1000000000000000000/6886350524917807),7,6,(622276751420646661/125000000000000000)⟩,⟨(1000000000000000000/993113649475082193),0,2,(3455085428224729/500000000000000000)⟩,(41144311668062619/1000000000000000000)⟩
theorem valid813 : certificate813.Valid := by decide +kernel
theorem sound813 : 0 ≤ cappedLabelEntropy (certificate813.rho:ℝ) ∧ cappedLabelEntropy (certificate813.rho:ℝ) ≤ (certificate813.bound:ℝ) := rat_label_entropy_certificate_sound certificate813 valid813

def certificate814 : RatLabelEntropyCertificate := ⟨(606282932568919/50000000000000000),⟨(50000000000000000/606282932568919),6,8,(882486304374159669/200000000000000000)⟩,⟨(50000000000000000/49393717067431081),0,3,(12199774192766813/1000000000000000000)⟩,(13111096470413749/200000000000000000)⟩
theorem valid814 : certificate814.Valid := by decide +kernel
theorem sound814 : 0 ≤ cappedLabelEntropy (certificate814.rho:ℝ) ∧ cappedLabelEntropy (certificate814.rho:ℝ) ≤ (certificate814.bound:ℝ) := rat_label_entropy_certificate_sound certificate814 valid814

def certificate815 : RatLabelEntropyCertificate := ⟨(83858799997060961/1000000000000000000),⟨(1000000000000000000/83858799997060961),3,10,(2478620846940509023/1000000000000000000)⟩,⟨(1000000000000000000/916141200002939039),0,5,(87584777712837847/1000000000000000000)⟩,(288094193227959931/1000000000000000000)⟩
theorem valid815 : certificate815.Valid := by decide +kernel
theorem sound815 : 0 ≤ cappedLabelEntropy (certificate815.rho:ℝ) ∧ cappedLabelEntropy (certificate815.rho:ℝ) ≤ (certificate815.bound:ℝ) := rat_label_entropy_certificate_sound certificate815 valid815

def certificate816 : RatLabelEntropyCertificate := ⟨(2944414485762031/31250000000000000),⟨(31250000000000000/2944414485762031),3,9,(236210939522507283/100000000000000000)⟩,⟨(31250000000000000/28305585514237969),0,6,(98960223013444237/1000000000000000000)⟩,(312196997608652831/1000000000000000000)⟩
theorem valid816 : certificate816.Valid := by decide +kernel
theorem sound816 : 0 ≤ cappedLabelEntropy (certificate816.rho:ℝ) ∧ cappedLabelEntropy (certificate816.rho:ℝ) ≤ (certificate816.bound:ℝ) := rat_label_entropy_certificate_sound certificate816 valid816

def certificate817 : RatLabelEntropyCertificate := ⟨(8246585990984411/1000000000000000000),⟨(1000000000000000000/8246585990984411),6,15,(2398977991778494663/500000000000000000)⟩,⟨(1000000000000000000/991753414009015589),0,3,(4140388592366843/500000000000000000)⟩,(23889622821484249/500000000000000000)⟩
theorem valid817 : certificate817.Valid := by decide +kernel
theorem sound817 : 0 ≤ cappedLabelEntropy (certificate817.rho:ℝ) ∧ cappedLabelEntropy (certificate817.rho:ℝ) ≤ (certificate817.bound:ℝ) := rat_label_entropy_certificate_sound certificate817 valid817

def certificate818 : RatLabelEntropyCertificate := ⟨(6752348362323133/1000000000000000000),⟨(1000000000000000000/6752348362323133),7,6,(4997864929073441273/1000000000000000000)⟩,⟨(1000000000000000000/993247651637676867),0,2,(3387624305858477/500000000000000000)⟩,(5059603105223821/125000000000000000)⟩
theorem valid818 : certificate818.Valid := by decide +kernel
theorem sound818 : 0 ≤ cappedLabelEntropy (certificate818.rho:ℝ) ∧ cappedLabelEntropy (certificate818.rho:ℝ) ≤ (certificate818.bound:ℝ) := rat_label_entropy_certificate_sound certificate818 valid818

def certificate819 : RatLabelEntropyCertificate := ⟨(3564932705845333/500000000000000000),⟨(500000000000000000/3564932705845333),7,6,(4943462921074812901/1000000000000000000)⟩,⟨(500000000000000000/496435067294154667),0,3,(7155404367364661/1000000000000000000)⟩,(42350612592205741/1000000000000000000)⟩
theorem valid819 : certificate819.Valid := by decide +kernel
theorem sound819 : 0 ≤ cappedLabelEntropy (certificate819.rho:ℝ) ∧ cappedLabelEntropy (certificate819.rho:ℝ) ≤ (certificate819.bound:ℝ) := rat_label_entropy_certificate_sound certificate819 valid819

end Cycle12.CutLabelCertificates.Entropy040
