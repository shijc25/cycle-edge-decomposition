import Cycle12.RationalMajorityCertificate

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MajorityCertificates.Batch008

def certificate320 : RatMajorityCertificate := ⟨0,(1006105021496533967/1000000000000000000),(69812903/58135000),(44193867838567806877/100000000000000000000),(22096933919283903439/50000000000000000000),(728683346211374957/1000000000000000000),false⟩
theorem valid320 : certificate320.Valid := by decide +kernel
theorem bound320 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate320.a certificate320.b certificate320.c x ≤ (certificate320.bound:ℝ) :=
  rat_majority_certificate_sound certificate320 valid320 x hx0 hx1

def certificate321 : RatMajorityCertificate := ⟨(53264152808703873/250000000000000000),(197936923767537811529553740811045809/250000000000000000000000000000000000),(69812903/58135000),(39537892544397447267/100000000000000000000),(9884473136099361817/25000000000000000000),(728683346211374957/1000000000000000000),false⟩
theorem valid321 : certificate321.Valid := by decide +kernel
theorem bound321 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate321.a certificate321.b certificate321.c x ≤ (certificate321.bound:ℝ) :=
  rat_majority_certificate_sound certificate321 valid321 x hx0 hx1

def certificate322 : RatMajorityCertificate := ⟨0,(1006105021496533967/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(271599591717148627/500000000000000000),false⟩
theorem valid322 : certificate322.Valid := by decide +kernel
theorem bound322 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate322.a certificate322.b certificate322.c x ≤ (certificate322.bound:ℝ) :=
  rat_majority_certificate_sound certificate322 valid322 x hx0 hx1

def certificate323 : RatMajorityCertificate := ⟨(131156861512469561/1000000000000000000),(874147444525112850822178087909921513/1000000000000000000000000000000000000),1,(36487728527481989983/100000000000000000000),(1140241516483812187/3125000000000000000),(271599591717148627/500000000000000000),false⟩
theorem valid323 : certificate323.Valid := by decide +kernel
theorem bound323 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate323.a certificate323.b certificate323.c x ≤ (certificate323.bound:ℝ) :=
  rat_majority_certificate_sound certificate323 valid323 x hx0 hx1

def certificate324 : RatMajorityCertificate := ⟨0,(1006151986511642219/1000000000000000000),(237260623/197560000),(22097820651485778199/50000000000000000000),(44195641302971556399/100000000000000000000),(364375718389096899/500000000000000000),false⟩
theorem valid324 : certificate324.Valid := by decide +kernel
theorem bound324 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate324.a certificate324.b certificate324.c x ≤ (certificate324.bound:ℝ) :=
  rat_majority_certificate_sound certificate324 valid324 x hx0 hx1

def certificate325 : RatMajorityCertificate := ⟨(53188439374370287/250000000000000000),(198022342691933841838910232631653147/250000000000000000000000000000000000),(237260623/197560000),(39547972603518933293/100000000000000000000),(19773986301759466647/50000000000000000000),(364375718389096899/500000000000000000),false⟩
theorem valid325 : certificate325.Valid := by decide +kernel
theorem bound325 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate325.a certificate325.b certificate325.c x ≤ (certificate325.bound:ℝ) :=
  rat_majority_certificate_sound certificate325 valid325 x hx0 hx1

def certificate326 : RatMajorityCertificate := ⟨0,(1006151986511642219/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(13580574903548503/25000000000000000),false⟩
theorem valid326 : certificate326.Valid := by decide +kernel
theorem bound326 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate326.a certificate326.b certificate326.c x ≤ (certificate326.bound:ℝ) :=
  rat_majority_certificate_sound certificate326 valid326 x hx0 hx1

def certificate327 : RatMajorityCertificate := ⟨(131179027324106831/1000000000000000000),(874165947580827136686815982794102011/1000000000000000000000000000000000000),1,(36487333958047753023/100000000000000000000),(570114593094496141/1562500000000000000),(13580574903548503/25000000000000000),false⟩
theorem valid327 : certificate327.Valid := by decide +kernel
theorem bound327 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate327.a certificate327.b certificate327.c x ≤ (certificate327.bound:ℝ) :=
  rat_majority_certificate_sound certificate327 valid327 x hx0 hx1

def certificate328 : RatMajorityCertificate := ⟨0,(503099469496617661/500000000000000000),(2375581607/1974620000),(4424270087824744313/10000000000000000000),(44242700878247443131/100000000000000000000),(22862477654785629/31250000000000000),false⟩
theorem valid328 : certificate328.Valid := by decide +kernel
theorem bound328 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate328.a certificate328.b certificate328.c x ≤ (certificate328.bound:ℝ) :=
  rat_majority_certificate_sound certificate328 valid328 x hx0 hx1

def certificate329 : RatMajorityCertificate := ⟨(13879221048836747/62500000000000000),(24461088096842547035337384934011233/31250000000000000000000000000000000),(2375581607/1974620000),(39348582190253839601/100000000000000000000),(19674291095126919801/50000000000000000000),(22862477654785629/31250000000000000),false⟩
theorem valid329 : certificate329.Valid := by decide +kernel
theorem bound329 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate329.a certificate329.b certificate329.c x ≤ (certificate329.bound:ℝ) :=
  rat_majority_certificate_sound certificate329 valid329 x hx0 hx1

def certificate330 : RatMajorityCertificate := ⟨0,(503099469496617661/500000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(67902537242180051/125000000000000000),false⟩
theorem valid330 : certificate330.Valid := by decide +kernel
theorem bound330 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate330.a certificate330.b certificate330.c x ≤ (certificate330.bound:ℝ) :=
  rat_majority_certificate_sound certificate330 valid330 x hx0 hx1

def certificate331 : RatMajorityCertificate := ⟨(32737626346176089/250000000000000000),(109304584926814731270873313386692171/125000000000000000000000000000000000),1,(9123202400476758701/25000000000000000000),(7298561920381406961/20000000000000000000),(67902537242180051/125000000000000000),false⟩
theorem valid331 : certificate331.Valid := by decide +kernel
theorem bound331 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate331.a certificate331.b certificate331.c x ≤ (certificate331.bound:ℝ) :=
  rat_majority_certificate_sound certificate331 valid331 x hx0 hx1

def certificate332 : RatMajorityCertificate := ⟨0,(1006221296237558437/1000000000000000000),(789001693/660470000),(2202649511398798671/5000000000000000000),(44052990227975973421/100000000000000000000),(722621634883513943/1000000000000000000),false⟩
theorem valid332 : certificate332.Valid := by decide +kernel
theorem bound332 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate332.a certificate332.b certificate332.c x ≤ (certificate332.bound:ℝ) :=
  rat_majority_certificate_sound certificate332 valid332 x hx0 hx1

def certificate333 : RatMajorityCertificate := ⟨(10418065101838599/50000000000000000),(39828185840818615519238672595290237/50000000000000000000000000000000000),(789001693/660470000),(19757585165098426443/50000000000000000000),(39515170330196852887/100000000000000000000),(722621634883513943/1000000000000000000),false⟩
theorem valid333 : certificate333.Valid := by decide +kernel
theorem bound333 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate333.a certificate333.b certificate333.c x ≤ (certificate333.bound:ℝ) :=
  rat_majority_certificate_sound certificate333 valid333 x hx0 hx1

def certificate334 : RatMajorityCertificate := ⟨0,(1006221296237558437/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(543077226223952569/1000000000000000000),false⟩
theorem valid334 : certificate334.Valid := by decide +kernel
theorem bound334 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate334.a certificate334.b certificate334.c x ≤ (certificate334.bound:ℝ) :=
  rat_majority_certificate_sound certificate334 valid334 x hx0 hx1

def certificate335 : RatMajorityCertificate := ⟨(129497263413152377/1000000000000000000),(875918391986759701277373644077045251/1000000000000000000000000000000000000),1,(3652684578717303357/10000000000000000000),(36526845787173033571/100000000000000000000),(543077226223952569/1000000000000000000),false⟩
theorem valid335 : certificate335.Valid := by decide +kernel
theorem bound335 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate335.a certificate335.b certificate335.c x ≤ (certificate335.bound:ℝ) :=
  rat_majority_certificate_sound certificate335 valid335 x hx0 hx1

def certificate336 : RatMajorityCertificate := ⟨0,(503133960750343231/500000000000000000),(1182319897/990240000),(44038710932094496883/100000000000000000000),(11009677733023624221/25000000000000000000),(28874971334208299/40000000000000000),false⟩
theorem valid336 : certificate336.Valid := by decide +kernel
theorem bound336 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate336.a certificate336.b certificate336.c x ≤ (certificate336.bound:ℝ) :=
  rat_majority_certificate_sound certificate336 valid336 x hx0 hx1

def certificate337 : RatMajorityCertificate := ⟨(206287873742639851/1000000000000000000),(399343525779442112212387591731301419/500000000000000000000000000000000000),(1182319897/990240000),(9888708974922682069/25000000000000000000),(39554835899690728277/100000000000000000000),(28874971334208299/40000000000000000),false⟩
theorem valid337 : certificate337.Valid := by decide +kernel
theorem bound337 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate337.a certificate337.b certificate337.c x ≤ (certificate337.bound:ℝ) :=
  rat_majority_certificate_sound certificate337 valid337 x hx0 hx1

def certificate338 : RatMajorityCertificate := ⟨0,(503133960750343231/500000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(543098246332260281/1000000000000000000),false⟩
theorem valid338 : certificate338.Valid := by decide +kernel
theorem bound338 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate338.a certificate338.b certificate338.c x ≤ (certificate338.bound:ℝ) :=
  rat_majority_certificate_sound certificate338 valid338 x hx0 hx1

def certificate339 : RatMajorityCertificate := ⟨(129494073838729221/1000000000000000000),(437981094486165994911050183380746949/500000000000000000000000000000000000),1,(36527042219029405263/100000000000000000000),(2282940138689337829/6250000000000000000),(543098246332260281/1000000000000000000),false⟩
theorem valid339 : certificate339.Valid := by decide +kernel
theorem bound339 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate339.a certificate339.b certificate339.c x ≤ (certificate339.bound:ℝ) :=
  rat_majority_certificate_sound certificate339 valid339 x hx0 hx1

def certificate340 : RatMajorityCertificate := ⟨0,(1006314523509792583/1000000000000000000),(2363211317/1979560000),(22017475340405295237/50000000000000000000),(1761398027232423619/4000000000000000000),(90228827115929721/125000000000000000),false⟩
theorem valid340 : certificate340.Valid := by decide +kernel
theorem bound340 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate340.a certificate340.b certificate340.c x ≤ (certificate340.bound:ℝ) :=
  rat_majority_certificate_sound certificate340 valid340 x hx0 hx1

def certificate341 : RatMajorityCertificate := ⟨(207129285185029963/1000000000000000000),(797877315583895215733527293229835571/1000000000000000000000000000000000000),(2363211317/1979560000),(39529081253814265621/100000000000000000000),(19764540626907132811/50000000000000000000),(90228827115929721/125000000000000000),false⟩
theorem valid341 : certificate341.Valid := by decide +kernel
theorem bound341 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate341.a certificate341.b certificate341.c x ≤ (certificate341.bound:ℝ) :=
  rat_majority_certificate_sound certificate341 valid341 x hx0 hx1

def certificate342 : RatMajorityCertificate := ⟨0,(1006314523509792583/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(135774498584397983/250000000000000000),false⟩
theorem valid342 : certificate342.Valid := by decide +kernel
theorem bound342 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate342.a certificate342.b certificate342.c x ≤ (certificate342.bound:ℝ) :=
  rat_majority_certificate_sound certificate342 valid342 x hx0 hx1

def certificate343 : RatMajorityCertificate := ⟨(64644396728893369/500000000000000000),(438104666463081966572002711685917873/500000000000000000000000000000000000),1,(2283247248862549519/6250000000000000000),(7306391196360158461/20000000000000000000),(135774498584397983/250000000000000000),false⟩
theorem valid343 : certificate343.Valid := by decide +kernel
theorem bound343 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate343.a certificate343.b certificate343.c x ≤ (certificate343.bound:ℝ) :=
  rat_majority_certificate_sound certificate343 valid343 x hx0 hx1

def certificate344 : RatMajorityCertificate := ⟨0,(1006361099205123483/1000000000000000000),(590249611/494662500),(22011052416298014221/50000000000000000000),(44022104832596028443/100000000000000000000),(180293227268081231/250000000000000000),false⟩
theorem valid344 : certificate344.Valid := by decide +kernel
theorem bound344 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate344.a certificate344.b certificate344.c x ≤ (certificate344.bound:ℝ) :=
  rat_majority_certificate_sound certificate344 valid344 x hx0 hx1

def certificate345 : RatMajorityCertificate := ⟨(205379667634775061/1000000000000000000),(799674991129808329231620528566142537/1000000000000000000000000000000000000),(590249611/494662500),(618150942672135153/1562500000000000000),(39561660331016649793/100000000000000000000),(180293227268081231/250000000000000000),false⟩
theorem valid345 : certificate345.Valid := by decide +kernel
theorem bound345 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate345.a certificate345.b certificate345.c x ≤ (certificate345.bound:ℝ) :=
  rat_majority_certificate_sound certificate345 valid345 x hx0 hx1

def certificate346 : RatMajorityCertificate := ⟨0,(1006361099205123483/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(67889885404007741/125000000000000000),false⟩
theorem valid346 : certificate346.Valid := by decide +kernel
theorem bound346 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate346.a certificate346.b certificate346.c x ≤ (certificate346.bound:ℝ) :=
  rat_majority_certificate_sound certificate346 valid346 x hx0 hx1

def certificate347 : RatMajorityCertificate := ⟨(6464320958561703/50000000000000000),(43812613814783301229358327810228451/50000000000000000000000000000000000),1,(365321329881829327772897/1000000000000000000000000),(182660664940914663886449/500000000000000000000000),(67889885404007741/125000000000000000),false⟩
theorem valid347 : certificate347.Valid := by decide +kernel
theorem bound347 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate347.a certificate347.b certificate347.c x ≤ (certificate347.bound:ℝ) :=
  rat_majority_certificate_sound certificate347 valid347 x hx0 hx1

def certificate348 : RatMajorityCertificate := ⟨0,(1006407645524895643/1000000000000000000),(98308697/82406250),(1375506811961916411/3125000000000000000),(44016217982781325153/100000000000000000000),(720999644089700869/1000000000000000000),false⟩
theorem valid348 : certificate348.Valid := by decide +kernel
theorem bound348 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate348.a certificate348.b certificate348.c x ≤ (certificate348.bound:ℝ) :=
  rat_majority_certificate_sound certificate348 valid348 x hx0 hx1

def certificate349 : RatMajorityCertificate := ⟨(205761494096417987/1000000000000000000),(799327704711634902019309361716869359/1000000000000000000000000000000000000),(98308697/82406250),(39545745091841785751/100000000000000000000),(4943218136480223219/12500000000000000000),(720999644089700869/1000000000000000000),false⟩
theorem valid349 : certificate349.Valid := by decide +kernel
theorem bound349 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate349.a certificate349.b certificate349.c x ≤ (certificate349.bound:ℝ) :=
  rat_majority_certificate_sound certificate349 valid349 x hx0 hx1

def certificate350 : RatMajorityCertificate := ⟨0,(1006407645524895643/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(54311863761822323/100000000000000000),false⟩
theorem valid350 : certificate350.Valid := by decide +kernel
theorem bound350 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate350.a certificate350.b certificate350.c x ≤ (certificate350.bound:ℝ) :=
  rat_majority_certificate_sound certificate350 valid350 x hx0 hx1

def certificate351 : RatMajorityCertificate := ⟨(25815855525290237/200000000000000000),(175300254728560913153795813288262609/200000000000000000000000000000000000),1,(9134271895398344833/25000000000000000000),(36537087581593379333/100000000000000000000),(54311863761822323/100000000000000000),false⟩
theorem valid351 : certificate351.Valid := by decide +kernel
theorem bound351 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate351.a certificate351.b certificate351.c x ≤ (certificate351.bound:ℝ) :=
  rat_majority_certificate_sound certificate351 valid351 x hx0 hx1

def certificate352 : RatMajorityCertificate := ⟨0,(251613539851378817/250000000000000000),(1178699991/988430000),(4400540119386577411/10000000000000000000),(44005401193865774111/100000000000000000000),(72046861052378831/100000000000000000),false⟩
theorem valid352 : certificate352.Valid := by decide +kernel
theorem bound352 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate352.a certificate352.b certificate352.c x ≤ (certificate352.bound:ℝ) :=
  rat_majority_certificate_sound certificate352 valid352 x hx0 hx1

def certificate353 : RatMajorityCertificate := ⟨(102237646465659967/500000000000000000),(100082393792390895731708973171280961/125000000000000000000000000000000000),(1178699991/988430000),(19784121945430693603/50000000000000000000),(39568243890861387207/100000000000000000000),(72046861052378831/100000000000000000),false⟩
theorem valid353 : certificate353.Valid := by decide +kernel
theorem bound353 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate353.a certificate353.b certificate353.c x ≤ (certificate353.bound:ℝ) :=
  rat_majority_certificate_sound certificate353 valid353 x hx0 hx1

def certificate354 : RatMajorityCertificate := ⟨0,(251613539851378817/250000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(108627948630465081/200000000000000000),false⟩
theorem valid354 : certificate354.Valid := by decide +kernel
theorem bound354 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate354.a certificate354.b certificate354.c x ≤ (certificate354.bound:ℝ) :=
  rat_majority_certificate_sound certificate354 valid354 x hx0 hx1

def certificate355 : RatMajorityCertificate := ⟨(129077277168819047/1000000000000000000),(219135949228554696596152397478072601/250000000000000000000000000000000000),1,(18268627722777504109/50000000000000000000),(36537255445555008219/100000000000000000000),(108627948630465081/200000000000000000),false⟩
theorem valid355 : certificate355.Valid := by decide +kernel
theorem bound355 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate355.a certificate355.b certificate355.c x ≤ (certificate355.bound:ℝ) :=
  rat_majority_certificate_sound certificate355 valid355 x hx0 hx1

def certificate356 : RatMajorityCertificate := ⟨0,(100650067084646431/100000000000000000),(588921587/493992500),(43997944100092648399/100000000000000000000),(109994860250231621/250000000000000000),(720199355866020947/1000000000000000000),false⟩
theorem valid356 : certificate356.Valid := by decide +kernel
theorem bound356 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate356.a certificate356.b certificate356.c x ≤ (certificate356.bound:ℝ) :=
  rat_majority_certificate_sound certificate356 valid356 x hx0 hx1

def certificate357 : RatMajorityCertificate := ⟨(40902284325501317/200000000000000000),(16013195755652296447460832230150373/20000000000000000000000000000000000),(588921587/493992500),(39559727140894659359/100000000000000000000),(247248294630591621/625000000000000000),(720199355866020947/1000000000000000000),false⟩
theorem valid357 : certificate357.Valid := by decide +kernel
theorem bound357 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate357.a certificate357.b certificate357.c x ≤ (certificate357.bound:ℝ) :=
  rat_majority_certificate_sound certificate357 valid357 x hx0 hx1

def certificate358 : RatMajorityCertificate := ⟨0,(100650067084646431/100000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(543139132450287921/1000000000000000000),false⟩
theorem valid358 : certificate358.Valid := by decide +kernel
theorem bound358 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate358.a certificate358.b certificate358.c x ≤ (certificate358.bound:ℝ) :=
  rat_majority_certificate_sound certificate358 valid358 x hx0 hx1

def certificate359 : RatMajorityCertificate := ⟨(128868450763854803/1000000000000000000),(87679448870169989474118666123841907/100000000000000000000000000000000000),1,(18271123380401721481/50000000000000000000),(36542246760803442963/100000000000000000000),(543139132450287921/1000000000000000000),false⟩
theorem valid359 : certificate359.Valid := by decide +kernel
theorem bound359 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate359.a certificate359.b certificate359.c x ≤ (certificate359.bound:ℝ) :=
  rat_majority_certificate_sound certificate359 valid359 x hx0 hx1

end Cycle12.MajorityCertificates.Batch008
