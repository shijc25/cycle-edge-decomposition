import Cycle12.RationalLabelEntropy
import Cycle12.RationalMinorityBudget

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CutLabelCertificates.Entropy016

def certificate320 : RatLabelEntropyCertificate := ⟨(128090658636100143/1000000000000000000),⟨(1000000000000000000/128090658636100143),2,15,(2055016995173233941/1000000000000000000)⟩,⟨(1000000000000000000/871909341363899857),0,7,(13706982680383341/100000000000000000)⟩,(19137047141475659/50000000000000000)⟩
theorem valid320 : certificate320.Valid := by decide +kernel
theorem sound320 : 0 ≤ cappedLabelEntropy (certificate320.rho:ℝ) ∧ cappedLabelEntropy (certificate320.rho:ℝ) ≤ (certificate320.bound:ℝ) := rat_label_entropy_certificate_sound certificate320 valid320

def certificate321 : RatLabelEntropyCertificate := ⟨(64738296620473889/500000000000000000),⟨(500000000000000000/64738296620473889),2,15,(1022127580676716051/500000000000000000)⟩,⟨(500000000000000000/435261703379526111),0,6,(13866063126801481/100000000000000000)⟩,(24086907445128713/62500000000000000)⟩
theorem valid321 : certificate321.Valid := by decide +kernel
theorem sound321 : 0 ≤ cappedLabelEntropy (certificate321.rho:ℝ) ∧ cappedLabelEntropy (certificate321.rho:ℝ) ≤ (certificate321.bound:ℝ) := rat_label_entropy_certificate_sound certificate321 valid321

def certificate322 : RatLabelEntropyCertificate := ⟨(131774943201269773/1000000000000000000),⟨(1000000000000000000/131774943201269773),2,15,(405331957453815439/200000000000000000)⟩,⟨(1000000000000000000/868225056798730227),0,6,(141304315903375401/1000000000000000000)⟩,(77949385211358791/200000000000000000)⟩
theorem valid322 : certificate322.Valid := by decide +kernel
theorem sound322 : 0 ≤ cappedLabelEntropy (certificate322.rho:ℝ) ∧ cappedLabelEntropy (certificate322.rho:ℝ) ≤ (certificate322.bound:ℝ) := rat_label_entropy_certificate_sound certificate322 valid322

def certificate323 : RatLabelEntropyCertificate := ⟨(134108889316480869/1000000000000000000),⟨(1000000000000000000/134108889316480869),2,15,(2009103202178000021/1000000000000000000)⟩,⟨(1000000000000000000/865891110683519131),0,6,(14399611656615723/100000000000000000)⟩,(12316361133558127/31250000000000000)⟩
theorem valid323 : certificate323.Valid := by decide +kernel
theorem sound323 : 0 ≤ cappedLabelEntropy (certificate323.rho:ℝ) ∧ cappedLabelEntropy (certificate323.rho:ℝ) ≤ (certificate323.bound:ℝ) := rat_label_entropy_certificate_sound certificate323 valid323

def certificate324 : RatLabelEntropyCertificate := ⟨(34107414778527103/250000000000000000),⟨(250000000000000000/34107414778527103),2,14,(1991946115024355403/1000000000000000000)⟩,⟨(250000000000000000/215892585221472897),0,7,(73339962254704937/500000000000000000)⟩,(199214480928076661/500000000000000000)⟩
theorem valid324 : certificate324.Valid := by decide +kernel
theorem sound324 : 0 ≤ cappedLabelEntropy (certificate324.rho:ℝ) ∧ cappedLabelEntropy (certificate324.rho:ℝ) ≤ (certificate324.bound:ℝ) := rat_label_entropy_certificate_sound certificate324 valid324

def certificate325 : RatLabelEntropyCertificate := ⟨(138893626769609231/1000000000000000000),⟨(1000000000000000000/138893626769609231),2,14,(123377932116415593/62500000000000000)⟩,⟨(1000000000000000000/861106373230390769),0,6,(149537236041130191/1000000000000000000)⟩,(201475001135006139/500000000000000000)⟩
theorem valid325 : certificate325.Valid := by decide +kernel
theorem sound325 : 0 ≤ cappedLabelEntropy (certificate325.rho:ℝ) ∧ cappedLabelEntropy (certificate325.rho:ℝ) ≤ (certificate325.bound:ℝ) := rat_label_entropy_certificate_sound certificate325 valid325

def certificate326 : RatLabelEntropyCertificate := ⟨(140248772671899331/1000000000000000000),⟨(1000000000000000000/140248772671899331),2,14,(392867497124024383/200000000000000000)⟩,⟨(1000000000000000000/859751227328100669),0,7,(151112202130099191/1000000000000000000)⟩,(50676852839653951/125000000000000000)⟩
theorem valid326 : certificate326.Valid := by decide +kernel
theorem sound326 : 0 ≤ cappedLabelEntropy (certificate326.rho:ℝ) ∧ cappedLabelEntropy (certificate326.rho:ℝ) ≤ (certificate326.bound:ℝ) := rat_label_entropy_certificate_sound certificate326 valid326

def certificate327 : RatLabelEntropyCertificate := ⟨(3560711624202423/25000000000000000),⟨(25000000000000000/3560711624202423),2,14,(121807212846350631/62500000000000000)⟩,⟨(25000000000000000/21439288375797577),0,6,(4801583770118717/31250000000000000)⟩,(81869495924473399/200000000000000000)⟩
theorem valid327 : certificate327.Valid := by decide +kernel
theorem sound327 : 0 ≤ cappedLabelEntropy (certificate327.rho:ℝ) ∧ cappedLabelEntropy (certificate327.rho:ℝ) ≤ (certificate327.bound:ℝ) := rat_label_entropy_certificate_sound certificate327 valid327

def certificate328 : RatLabelEntropyCertificate := ⟨(144790213801511433/1000000000000000000),⟨(1000000000000000000/144790213801511433),2,14,(966234692779072269/500000000000000000)⟩,⟨(1000000000000000000/855209786198488567),0,6,(31281695233470693/200000000000000000)⟩,(41356471496255293/100000000000000000)⟩
theorem valid328 : certificate328.Valid := by decide +kernel
theorem sound328 : 0 ≤ cappedLabelEntropy (certificate328.rho:ℝ) ∧ cappedLabelEntropy (certificate328.rho:ℝ) ≤ (certificate328.bound:ℝ) := rat_label_entropy_certificate_sound certificate328 valid328

def certificate329 : RatLabelEntropyCertificate := ⟨(123048184451893/1000000000000000000),⟨(1000000000000000000/123048184451893),12,16,(9002934535791987249/1000000000000000000)⟩,⟨(1000000000000000000/999876951815548107),0,1,(61527877750409/500000000000000000)⟩,(76927210192623/62500000000000000)⟩
theorem valid329 : certificate329.Valid := by decide +kernel
theorem sound329 : 0 ≤ cappedLabelEntropy (certificate329.rho:ℝ) ∧ cappedLabelEntropy (certificate329.rho:ℝ) ≤ (certificate329.bound:ℝ) := rat_label_entropy_certificate_sound certificate329 valid329

def certificate330 : RatLabelEntropyCertificate := ⟨(95005437970157/500000000000000000),⟨(500000000000000000/95005437970157),12,8,(8568429245650910453/1000000000000000000)⟩,⟨(500000000000000000/499904994562029843),0,1,(95014465146927/500000000000000000)⟩,(1818087569129089/1000000000000000000)⟩
theorem valid330 : certificate330.Valid := by decide +kernel
theorem sound330 : 0 ≤ cappedLabelEntropy (certificate330.rho:ℝ) ∧ cappedLabelEntropy (certificate330.rho:ℝ) ≤ (certificate330.bound:ℝ) := rat_label_entropy_certificate_sound certificate330 valid330

def certificate331 : RatLabelEntropyCertificate := ⟨(4631370286433/20000000000000000),⟨(20000000000000000/4631370286433),12,5,(1674126954006419907/200000000000000000)⟩,⟨(20000000000000000/19995368629713567),0,1,(23159533044999/100000000000000000)⟩,(1084958578944437/500000000000000000)⟩
theorem valid331 : certificate331.Valid := by decide +kernel
theorem sound331 : 0 ≤ cappedLabelEntropy (certificate331.rho:ℝ) ∧ cappedLabelEntropy (certificate331.rho:ℝ) ≤ (certificate331.bound:ℝ) := rat_label_entropy_certificate_sound certificate331 valid331

def certificate332 : RatLabelEntropyCertificate := ⟨(276104559413631/1000000000000000000),⟨(1000000000000000000/276104559413631),11,14,(409736546276655429/50000000000000000)⟩,⟨(1000000000000000000/999723895440586369),0,1,(276142683295109/1000000000000000000)⟩,(2538669010748779/1000000000000000000)⟩
theorem valid332 : certificate332.Valid := by decide +kernel
theorem sound332 : 0 ≤ cappedLabelEntropy (certificate332.rho:ℝ) ∧ cappedLabelEntropy (certificate332.rho:ℝ) ≤ (certificate332.bound:ℝ) := rat_label_entropy_certificate_sound certificate332 valid332

def certificate333 : RatLabelEntropyCertificate := ⟨(11838055171093/31250000000000000),⟨(31250000000000000/11838055171093),11,8,(3939227649199466933/500000000000000000)⟩,⟨(31250000000000000/31238161944828907),0,1,(378889535050329/1000000000000000000)⟩,(3363244836497269/1000000000000000000)⟩
theorem valid333 : certificate333.Valid := by decide +kernel
theorem sound333 : 0 ≤ cappedLabelEntropy (certificate333.rho:ℝ) ∧ cappedLabelEntropy (certificate333.rho:ℝ) ≤ (certificate333.bound:ℝ) := rat_label_entropy_certificate_sound certificate333 valid333

def certificate334 : RatLabelEntropyCertificate := ⟨(434020614724439/1000000000000000000),⟨(1000000000000000000/434020614724439),11,6,(967802315703357693/125000000000000000)⟩,⟨(1000000000000000000/999565979385275561),0,2,(217057414466517/500000000000000000)⟩,(151771826483783/40000000000000000)⟩
theorem valid334 : certificate334.Valid := by decide +kernel
theorem sound334 : 0 ≤ cappedLabelEntropy (certificate334.rho:ℝ) ∧ cappedLabelEntropy (certificate334.rho:ℝ) ≤ (certificate334.bound:ℝ) := rat_label_entropy_certificate_sound certificate334 valid334

def certificate335 : RatLabelEntropyCertificate := ⟨(491724441634071/1000000000000000000),⟨(1000000000000000000/491724441634071),10,16,(7617592076353755791/1000000000000000000)⟩,⟨(1000000000000000000/999508275558365929),0,1,(245922688871887/500000000000000000)⟩,(4237359735691207/1000000000000000000)⟩
theorem valid335 : certificate335.Valid := by decide +kernel
theorem sound335 : 0 ≤ cappedLabelEntropy (certificate335.rho:ℝ) ∧ cappedLabelEntropy (certificate335.rho:ℝ) ≤ (certificate335.bound:ℝ) := rat_label_entropy_certificate_sound certificate335 valid335

def certificate336 : RatLabelEntropyCertificate := ⟨(628227266730579/1000000000000000000),⟨(1000000000000000000/628227266730579),10,11,(7372608567263984213/1000000000000000000)⟩,⟨(1000000000000000000/999371772733269421),0,2,(157106171041563/250000000000000000)⟩,(1314925904882819/250000000000000000)⟩
theorem valid336 : certificate336.Valid := by decide +kernel
theorem sound336 : 0 ≤ cappedLabelEntropy (certificate336.rho:ℝ) ∧ cappedLabelEntropy (certificate336.rho:ℝ) ≤ (certificate336.bound:ℝ) := rat_label_entropy_certificate_sound certificate336 valid336

def certificate337 : RatLabelEntropyCertificate := ⟨(139969150142541/200000000000000000),⟨(200000000000000000/139969150142541),10,9,(726465060332755461/100000000000000000)⟩,⟨(200000000000000000/199860030849857459),0,2,(350045378533937/500000000000000000)⟩,(1156747131335541/200000000000000000)⟩
theorem valid337 : certificate337.Valid := by decide +kernel
theorem sound337 : 0 ≤ cappedLabelEntropy (certificate337.rho:ℝ) ∧ cappedLabelEntropy (certificate337.rho:ℝ) ≤ (certificate337.bound:ℝ) := rat_label_entropy_certificate_sound certificate337 valid337

def certificate338 : RatLabelEntropyCertificate := ⟨(156151995450157/200000000000000000),⟨(200000000000000000/156151995450157),10,8,(7155242782823134689/1000000000000000000)⟩,⟨(200000000000000000/199843848004549843),0,2,(390532464530801/500000000000000000)⟩,(6366982297166191/1000000000000000000)⟩
theorem valid338 : certificate338.Valid := by decide +kernel
theorem sound338 : 0 ≤ cappedLabelEntropy (certificate338.rho:ℝ) ∧ cappedLabelEntropy (certificate338.rho:ℝ) ≤ (certificate338.bound:ℝ) := rat_label_entropy_certificate_sound certificate338 valid338

def certificate339 : RatLabelEntropyCertificate := ⟨(427088509004189/500000000000000000),⟨(500000000000000000/427088509004189),10,6,(3532686052307597809/500000000000000000)⟩,⟨(500000000000000000/499572911490995811),0,2,(427271017535843/500000000000000000)⟩,(53819457658939/7812500000000000)⟩
theorem valid339 : certificate339.Valid := by decide +kernel
theorem sound339 : 0 ≤ cappedLabelEntropy (certificate339.rho:ℝ) ∧ cappedLabelEntropy (certificate339.rho:ℝ) ≤ (certificate339.bound:ℝ) := rat_label_entropy_certificate_sound certificate339 valid339

end Cycle12.CutLabelCertificates.Entropy016
