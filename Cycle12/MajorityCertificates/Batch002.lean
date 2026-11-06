import Cycle12.RationalMajorityCertificate

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MajorityCertificates.Batch002

def certificate80 : RatMajorityCertificate := ⟨0,(1001402157180979839/1000000000000000000),(2560826323/2156090000),(21948603489439408893/50000000000000000000),(43897206978878817787/100000000000000000000),(714451181226179937/1000000000000000000),false⟩
theorem valid80 : certificate80.Valid := by decide +kernel
theorem bound80 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate80.a certificate80.b certificate80.c x ≤ (certificate80.bound:ℝ) :=
  rat_majority_certificate_sound certificate80 valid80 x hx0 hx1

def certificate81 : RatMajorityCertificate := ⟨(107522427403203859/500000000000000000),(393027887843586274786355114514001299/500000000000000000000000000000000000),(2560826323/2156090000),(9788516818349190609/25000000000000000000),(39154067273396762437/100000000000000000000),(714451181226179937/1000000000000000000),false⟩
theorem valid81 : certificate81.Valid := by decide +kernel
theorem bound81 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate81.a certificate81.b certificate81.c x ≤ (certificate81.bound:ℝ) :=
  rat_majority_certificate_sound certificate81 valid81 x hx0 hx1

def certificate82 : RatMajorityCertificate := ⟨0,(1001402157180979839/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(540668774190226511/1000000000000000000),false⟩
theorem valid82 : certificate82.Valid := by decide +kernel
theorem bound82 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate82.a certificate82.b certificate82.c x ≤ (certificate82.bound:ℝ) :=
  rat_majority_certificate_sound certificate82 valid82 x hx0 hx1

def certificate83 : RatMajorityCertificate := ⟨(25525938083340001/200000000000000000),(174718701975471164869571001036760161/200000000000000000000000000000000000),1,(9139478067489023/25000000000000000),(36557912269956092001/100000000000000000000),(540668774190226511/1000000000000000000),false⟩
theorem valid83 : certificate83.Valid := by decide +kernel
theorem bound83 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate83.a certificate83.b certificate83.c x ≤ (certificate83.bound:ℝ) :=
  rat_majority_certificate_sound certificate83 valid83 x hx0 hx1

def certificate84 : RatMajorityCertificate := ⟨0,(1001525773469427903/1000000000000000000),(1277329181/1073755000),(43939670025718120367/100000000000000000000),(2746229376607382523/6250000000000000000),(716294502186056659/1000000000000000000),false⟩
theorem valid84 : certificate84.Valid := by decide +kernel
theorem bound84 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate84.a certificate84.b certificate84.c x ≤ (certificate84.bound:ℝ) :=
  rat_majority_certificate_sound certificate84 valid84 x hx0 hx1

def certificate85 : RatMajorityCertificate := ⟨(21595695640536701/100000000000000000),(78523931566943918577741741655031997/100000000000000000000000000000000000),(1277329181/1073755000),(39174530823958748931/100000000000000000000),(9793632705989687233/25000000000000000000),(716294502186056659/1000000000000000000),false⟩
theorem valid85 : certificate85.Valid := by decide +kernel
theorem bound85 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate85.a certificate85.b certificate85.c x ≤ (certificate85.bound:ℝ) :=
  rat_majority_certificate_sound certificate85 valid85 x hx0 hx1

def certificate86 : RatMajorityCertificate := ⟨0,(1001525773469427903/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(270391485148936349/500000000000000000),false⟩
theorem valid86 : certificate86.Valid := by decide +kernel
theorem bound86 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate86.a certificate86.b certificate86.c x ≤ (certificate86.bound:ℝ) :=
  rat_majority_certificate_sound certificate86 valid86 x hx0 hx1

def certificate87 : RatMajorityCertificate := ⟨(64082123929979743/500000000000000000),(436582988000177254461347151411031071/500000000000000000000000000000000000),1,(4568216573798239943/12500000000000000000),(7309146518077183909/20000000000000000000),(270391485148936349/500000000000000000),false⟩
theorem valid87 : certificate87.Valid := by decide +kernel
theorem bound87 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate87.a certificate87.b certificate87.c x ≤ (certificate87.bound:ℝ) :=
  rat_majority_certificate_sound certificate87 valid87 x hx0 hx1

def certificate88 : RatMajorityCertificate := ⟨0,(6260336141479543/6250000000000000),(318377779/267391250),(8792870907307758409/20000000000000000000),(21982177268269396023/50000000000000000000),(717482122458769771/1000000000000000000),false⟩
theorem valid88 : certificate88.Valid := by decide +kernel
theorem bound88 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate88.a certificate88.b certificate88.c x ≤ (certificate88.bound:ℝ) :=
  rat_majority_certificate_sound certificate88 valid88 x hx0 hx1

def certificate89 : RatMajorityCertificate := ⟨(43458472552792431/200000000000000000),(980002581920165407436067488260967/1250000000000000000000000000000000),(318377779/267391250),(9791262825049396637/25000000000000000000),(39165051300197586549/100000000000000000000),(717482122458769771/1000000000000000000),false⟩
theorem valid89 : certificate89.Valid := by decide +kernel
theorem bound89 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate89.a certificate89.b certificate89.c x ≤ (certificate89.bound:ℝ) :=
  rat_majority_certificate_sound certificate89 valid89 x hx0 hx1

def certificate90 : RatMajorityCertificate := ⟨0,(6260336141479543/6250000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(540853845065016211/1000000000000000000),false⟩
theorem valid90 : certificate90.Valid := by decide +kernel
theorem bound90 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate90.a certificate90.b certificate90.c x ≤ (certificate90.bound:ℝ) :=
  rat_majority_certificate_sound certificate90 valid90 x hx0 hx1

def certificate91 : RatMajorityCertificate := ⟨(128277281210955061/1000000000000000000),(5457277241783866314231095376182877/6250000000000000000000000000000000),1,(36543422127471942637/100000000000000000000),(18271711063735971319/50000000000000000000),(540853845065016211/1000000000000000000),false⟩
theorem valid91 : certificate91.Valid := by decide +kernel
theorem bound91 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate91.a certificate91.b certificate91.c x ≤ (certificate91.bound:ℝ) :=
  rat_majority_certificate_sound certificate91 valid91 x hx0 hx1

def certificate92 : RatMajorityCertificate := ⟨0,(500893023828301289/500000000000000000),(635398141/532740000),(22004972547158160639/50000000000000000000),(44009945094316321279/100000000000000000000),(719543974697637517/1000000000000000000),false⟩
theorem valid92 : certificate92.Valid := by decide +kernel
theorem bound92 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate92.a certificate92.b certificate92.c x ≤ (certificate92.bound:ℝ) :=
  rat_majority_certificate_sound certificate92 valid92 x hx0 hx1

def certificate93 : RatMajorityCertificate := ⟨(21900459753860577/100000000000000000),(39119514873488889522130390344616247/50000000000000000000000000000000000),(635398141/532740000),(19583610931765318213/50000000000000000000),(39167221863530636427/100000000000000000000),(719543974697637517/1000000000000000000),false⟩
theorem valid93 : certificate93.Valid := by decide +kernel
theorem bound93 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate93.a certificate93.b certificate93.c x ≤ (certificate93.bound:ℝ) :=
  rat_majority_certificate_sound certificate93 valid93 x hx0 hx1

def certificate94 : RatMajorityCertificate := ⟨0,(500893023828301289/500000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(108193218147927273/200000000000000000),false⟩
theorem valid94 : certificate94.Valid := by decide +kernel
theorem bound94 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate94.a certificate94.b certificate94.c x ≤ (certificate94.bound:ℝ) :=
  rat_majority_certificate_sound certificate94 valid94 x hx0 hx1

def certificate95 : RatMajorityCertificate := ⟨(64378546580434863/500000000000000000),(218199747047805480200818411796561593/250000000000000000000000000000000000),1,(4566567145074235529/12500000000000000000),(36532537160593884233/100000000000000000000),(108193218147927273/200000000000000000),false⟩
theorem valid95 : certificate95.Valid := by decide +kernel
theorem bound95 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate95.a certificate95.b certificate95.c x ≤ (certificate95.bound:ℝ) :=
  rat_majority_certificate_sound certificate95 valid95 x hx0 hx1

def certificate96 : RatMajorityCertificate := ⟨0,(500961216797485949/500000000000000000),(13139629/11000000),(8810171225061202073/20000000000000000000),(22025428062653005183/50000000000000000000),(90165445508105207/125000000000000000),false⟩
theorem valid96 : certificate96.Valid := by decide +kernel
theorem bound96 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate96.a certificate96.b certificate96.c x ≤ (certificate96.bound:ℝ) :=
  rat_majority_certificate_sound certificate96 valid96 x hx0 hx1

def certificate97 : RatMajorityCertificate := ⟨(219735236008387629/1000000000000000000),(390882385593441332959915155727075079/500000000000000000000000000000000000),(13139629/11000000),(19595463845197859773/50000000000000000000),(39190927690395719547/100000000000000000000),(90165445508105207/125000000000000000),false⟩
theorem valid97 : certificate97.Valid := by decide +kernel
theorem bound97 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate97.a certificate97.b certificate97.c x ≤ (certificate97.bound:ℝ) :=
  rat_majority_certificate_sound certificate97 valid97 x hx0 hx1

def certificate98 : RatMajorityCertificate := ⟨0,(500961216797485949/500000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(270542763937645347/500000000000000000),false⟩
theorem valid98 : certificate98.Valid := by decide +kernel
theorem bound98 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate98.a certificate98.b certificate98.c x ≤ (certificate98.bound:ℝ) :=
  rat_majority_certificate_sound certificate98 valid98 x hx0 hx1

def certificate99 : RatMajorityCertificate := ⟨(64643133035199377/500000000000000000),(218096905815827733500728342428946227/250000000000000000000000000000000000),1,(36520499340003920767/100000000000000000000),(285316401093780631/781250000000000000),(270542763937645347/500000000000000000),false⟩
theorem valid99 : certificate99.Valid := by decide +kernel
theorem bound99 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate99.a certificate99.b certificate99.c x ≤ (certificate99.bound:ℝ) :=
  rat_majority_certificate_sound certificate99 valid99 x hx0 hx1

def certificate100 : RatMajorityCertificate := ⟨0,(50103140545301121/50000000000000000),(315990113/264405000),(22032043565668723333/50000000000000000000),(44064087131337446667/100000000000000000000),(721760362590110581/1000000000000000000),false⟩
theorem valid100 : certificate100.Valid := by decide +kernel
theorem bound100 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate100.a certificate100.b certificate100.c x ≤ (certificate100.bound:ℝ) :=
  rat_majority_certificate_sound certificate100 valid100 x hx0 hx1

def certificate101 : RatMajorityCertificate := ⟨(1090606748903911/5000000000000000),(195872879506519022871991810415769/250000000000000000000000000000000),(315990113/264405000),(19624442347532052599/50000000000000000000),(39248884695064105199/100000000000000000000),(721760362590110581/1000000000000000000),false⟩
theorem valid101 : certificate101.Valid := by decide +kernel
theorem bound101 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate101.a certificate101.b certificate101.c x ≤ (certificate101.bound:ℝ) :=
  rat_majority_certificate_sound certificate101 valid101 x hx0 hx1

def certificate102 : RatMajorityCertificate := ⟨0,(50103140545301121/50000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(33823900852432337/62500000000000000),false⟩
theorem valid102 : certificate102.Valid := by decide +kernel
theorem bound102 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate102.a certificate102.b certificate102.c x ≤ (certificate102.bound:ℝ) :=
  rat_majority_certificate_sound certificate102 valid102 x hx0 hx1

def certificate103 : RatMajorityCertificate := ⟨(129589037041779829/1000000000000000000),(43610322809266593210243875411111691/50000000000000000000000000000000000),1,(36513772418585754787/100000000000000000000),(9128443104646438697/25000000000000000000),(33823900852432337/62500000000000000),false⟩
theorem valid103 : certificate103.Valid := by decide +kernel
theorem bound103 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate103.a certificate103.b certificate103.c x ≤ (certificate103.bound:ℝ) :=
  rat_majority_certificate_sound certificate103 valid103 x hx0 hx1

def certificate104 : RatMajorityCertificate := ⟨0,(1002207059086998663/1000000000000000000),(2520852341/2107660000),(22042675785144649621/50000000000000000000),(44085351570289299243/100000000000000000000),(9034524144343451/12500000000000000),false⟩
theorem valid104 : certificate104.Valid := by decide +kernel
theorem bound104 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate104.a certificate104.b certificate104.c x ≤ (certificate104.bound:ℝ) :=
  rat_majority_certificate_sound certificate104 valid104 x hx0 hx1

def certificate105 : RatMajorityCertificate := ⟨(218832863698886999/1000000000000000000),(782891218327751095596609655498917663/1000000000000000000000000000000000000),(2520852341/2107660000),(19626320090156455039/50000000000000000000),(39252640180312910079/100000000000000000000),(9034524144343451/12500000000000000),false⟩
theorem valid105 : certificate105.Valid := by decide +kernel
theorem bound105 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate105.a certificate105.b certificate105.c x ≤ (certificate105.bound:ℝ) :=
  rat_majority_certificate_sound certificate105 valid105 x hx0 hx1

def certificate106 : RatMajorityCertificate := ⟨0,(1002207059086998663/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(54128005773701011/100000000000000000),false⟩
theorem valid106 : certificate106.Valid := by decide +kernel
theorem bound106 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate106.a certificate106.b certificate106.c x ≤ (certificate106.bound:ℝ) :=
  rat_majority_certificate_sound certificate106 valid106 x hx0 hx1

def certificate107 : RatMajorityCertificate := ⟨(64941299220450341/500000000000000000),(436018901038482996385180759075105917/500000000000000000000000000000000000),1,(36507269652663325557/100000000000000000000),(18253634826331662779/50000000000000000000),(54128005773701011/100000000000000000),false⟩
theorem valid107 : certificate107.Valid := by decide +kernel
theorem bound107 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate107.a certificate107.b certificate107.c x ≤ (certificate107.bound:ℝ) :=
  rat_majority_certificate_sound certificate107 valid107 x hx0 hx1

def certificate108 : RatMajorityCertificate := ⟨0,(501177507253027723/500000000000000000),(125795333/105014000),(22063453783910409923/50000000000000000000),(44126907567820819847/100000000000000000000),(144916974469389171/200000000000000000),false⟩
theorem valid108 : certificate108.Valid := by decide +kernel
theorem bound108 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate108.a certificate108.b certificate108.c x ≤ (certificate108.bound:ℝ) :=
  rat_majority_certificate_sound certificate108 valid108 x hx0 hx1

def certificate109 : RatMajorityCertificate := ⟨(219602780565144143/1000000000000000000),(391117533103555138784741423329923611/500000000000000000000000000000000000),(125795333/105014000),(39276055112472622337/100000000000000000000),(19638027556236311169/50000000000000000000),(144916974469389171/200000000000000000),false⟩
theorem valid109 : certificate109.Valid := by decide +kernel
theorem bound109 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate109.a certificate109.b certificate109.c x ≤ (certificate109.bound:ℝ) :=
  rat_majority_certificate_sound certificate109 valid109 x hx0 hx1

def certificate110 : RatMajorityCertificate := ⟨0,(501177507253027723/500000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(135344543945537547/250000000000000000),false⟩
theorem valid110 : certificate110.Valid := by decide +kernel
theorem bound110 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate110.a certificate110.b certificate110.c x ≤ (certificate110.bound:ℝ) :=
  rat_majority_certificate_sound certificate110 valid110 x hx0 hx1

def certificate111 : RatMajorityCertificate := ⟨(8135313796971789/62500000000000000),(27246357913826747401211720934093553/31250000000000000000000000000000000),1,(18250518099053624597/50000000000000000000),(7300207239621449839/20000000000000000000),(135344543945537547/250000000000000000),false⟩
theorem valid111 : certificate111.Valid := by decide +kernel
theorem bound111 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate111.a certificate111.b certificate111.c x ≤ (certificate111.bound:ℝ) :=
  rat_majority_certificate_sound certificate111 valid111 x hx0 hx1

def certificate112 : RatMajorityCertificate := ⟨0,(200501307914580713/200000000000000000),(2508916953/2093090000),(44144324423599941863/100000000000000000000),(5518040552949992733/12500000000000000000),(725329278994270723/1000000000000000000),false⟩
theorem valid112 : certificate112.Valid := by decide +kernel
theorem bound112 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate112.a certificate112.b certificate112.c x ≤ (certificate112.bound:ℝ) :=
  rat_majority_certificate_sound certificate112 valid112 x hx0 hx1

def certificate113 : RatMajorityCertificate := ⟨(8769939402860369/40000000000000000),(6261667995978107564962886480536903/8000000000000000000000000000000000),(2508916953/2093090000),(4913064916049932539/12500000000000000000),(39304519328399460313/100000000000000000000),(725329278994270723/1000000000000000000),false⟩
theorem valid113 : certificate113.Valid := by decide +kernel
theorem bound113 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate113.a certificate113.b certificate113.c x ≤ (certificate113.bound:ℝ) :=
  rat_majority_certificate_sound certificate113 valid113 x hx0 hx1

def certificate114 : RatMajorityCertificate := ⟨0,(200501307914580713/200000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(27073949976986831/50000000000000000),false⟩
theorem valid114 : certificate114.Valid := by decide +kernel
theorem bound114 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate114.a certificate114.b certificate114.c x ≤ (certificate114.bound:ℝ) :=
  rat_majority_certificate_sound certificate114 valid114 x hx0 hx1

def certificate115 : RatMajorityCertificate := ⟨(16307205273710247/125000000000000000),(21793047503512136435939893143333889/25000000000000000000000000000000000),1,(18247285601097194501/50000000000000000000),(36494571202194389003/100000000000000000000),(27073949976986831/50000000000000000),false⟩
theorem valid115 : certificate115.Valid := by decide +kernel
theorem bound115 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate115.a certificate115.b certificate115.c x ≤ (certificate115.bound:ℝ) :=
  rat_majority_certificate_sound certificate115 valid115 x hx0 hx1

def certificate116 : RatMajorityCertificate := ⟨0,(200533513923474379/200000000000000000),(26860951/22380000),(11044800727306264097/25000000000000000000),(44179202909225056389/100000000000000000000),(726985747200879771/1000000000000000000),false⟩
theorem valid116 : certificate116.Valid := by decide +kernel
theorem bound116 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate116.a certificate116.b certificate116.c x ≤ (certificate116.bound:ℝ) :=
  rat_majority_certificate_sound certificate116 valid116 x hx0 hx1

def certificate117 : RatMajorityCertificate := ⟨(13805299116816367/62500000000000000),(9764919477557325208281486027638907/12500000000000000000000000000000000),(26860951/22380000),(39297649225644932959/100000000000000000000),(245610307660280831/625000000000000000),(726985747200879771/1000000000000000000),false⟩
theorem valid117 : certificate117.Valid := by decide +kernel
theorem bound117 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate117.a certificate117.b certificate117.c x ≤ (certificate117.bound:ℝ) :=
  rat_majority_certificate_sound certificate117 valid117 x hx0 hx1

def certificate118 : RatMajorityCertificate := ⟨0,(200533513923474379/200000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(27080359254875241/50000000000000000),false⟩
theorem valid118 : certificate118.Valid := by decide +kernel
theorem bound118 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate118.a certificate118.b certificate118.c x ≤ (certificate118.bound:ℝ) :=
  rat_majority_certificate_sound certificate118 valid118 x hx0 hx1

def certificate119 : RatMajorityCertificate := ⟨(818527096893163/6250000000000000),(1089192347040148704180294469229223/1250000000000000000000000000000000),1,(9120775560996164337/25000000000000000000),(36483102243984657349/100000000000000000000),(27080359254875241/50000000000000000),false⟩
theorem valid119 : certificate119.Valid := by decide +kernel
theorem bound119 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate119.a certificate119.b certificate119.c x ≤ (certificate119.bound:ℝ) :=
  rat_majority_certificate_sound certificate119 valid119 x hx0 hx1

end Cycle12.MajorityCertificates.Batch002
