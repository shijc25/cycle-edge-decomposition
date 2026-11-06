import Cycle12.RationalMajorityCertificate

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MajorityCertificates.Batch000

def certificate0 : RatMajorityCertificate := ⟨0,(62501760568896327/62500000000000000),(136781647/117500000),(10838797148011750149/25000000000000000000),(43355188592047000597/100000000000000000000),(173063789282714933/250000000000000000),false⟩
theorem valid0 : certificate0.Valid := by decide +kernel
theorem bound0 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate0.a certificate0.b certificate0.c x ≤ (certificate0.bound:ℝ) :=
  rat_majority_certificate_sound certificate0 valid0 x hx0 hx1

def certificate1 : RatMajorityCertificate := ⟨(21177035892260179/100000000000000000),(4926574029992663198730976438537467/6250000000000000000000000000000000),(136781647/117500000),(19335265452013861697/50000000000000000000),(7734106180805544679/20000000000000000000),(173063789282714933/250000000000000000),false⟩
theorem valid1 : certificate1.Valid := by decide +kernel
theorem bound1 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1.a certificate1.b certificate1.c x ≤ (certificate1.bound:ℝ) :=
  rat_majority_certificate_sound certificate1 valid1 x hx0 hx1

def certificate2 : RatMajorityCertificate := ⟨0,(62501760568896327/62500000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(33769084988993921/62500000000000000),false⟩
theorem valid2 : certificate2.Valid := by decide +kernel
theorem bound2 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate2.a certificate2.b certificate2.c x ≤ (certificate2.bound:ℝ) :=
  rat_majority_certificate_sound certificate2 valid2 x hx0 hx1

def certificate3 : RatMajorityCertificate := ⟨(13009200729360669/100000000000000000),(5437078107710420700583554347637237/6250000000000000000000000000000000),1,(912414306610877409/2500000000000000000),(36496572264435096361/100000000000000000000),(33769084988993921/62500000000000000),false⟩
theorem valid3 : certificate3.Valid := by decide +kernel
theorem bound3 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate3.a certificate3.b certificate3.c x ≤ (certificate3.bound:ℝ) :=
  rat_majority_certificate_sound certificate3 valid3 x hx0 hx1

def certificate4 : RatMajorityCertificate := ⟨0,(1000014084396847021/1000000000000000000),(54999269/47000000),(4349630998834275119/10000000000000000000),(43496309988342751191/100000000000000000000),(174683476400834809/250000000000000000),false⟩
theorem valid4 : certificate4.Valid := by decide +kernel
theorem bound4 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate4.a certificate4.b certificate4.c x ≤ (certificate4.bound:ℝ) :=
  rat_majority_certificate_sound certificate4 valid4 x hx0 hx1

def certificate5 : RatMajorityCertificate := ⟨(221441883142654059/1000000000000000000),(778569082378832229210440662652291761/1000000000000000000000000000000000000),(54999269/47000000),(19278199420801319303/50000000000000000000),(38556398841602638607/100000000000000000000),(174683476400834809/250000000000000000),false⟩
theorem valid5 : certificate5.Valid := by decide +kernel
theorem bound5 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate5.a certificate5.b certificate5.c x ≤ (certificate5.bound:ℝ) :=
  rat_majority_certificate_sound certificate5 valid5 x hx0 hx1

def certificate6 : RatMajorityCertificate := ⟨0,(1000014084396847021/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(135903700603807237/250000000000000000),false⟩
theorem valid6 : certificate6.Valid := by decide +kernel
theorem bound6 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate6.a certificate6.b certificate6.c x ≤ (certificate6.bound:ℝ) :=
  rat_majority_certificate_sound certificate6 valid6 x hx0 hx1

def certificate7 : RatMajorityCertificate := ⟨(39859885601182651/250000000000000000),(210143074095582020335313186873767329/250000000000000000000000000000000000),1,(4473475499638358407/12500000000000000000),(35787803997106867257/100000000000000000000),(135903700603807237/250000000000000000),false⟩
theorem valid7 : certificate7.Valid := by decide +kernel
theorem bound7 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate7.a certificate7.b certificate7.c x ≤ (certificate7.bound:ℝ) :=
  rat_majority_certificate_sound certificate7 valid7 x hx0 hx1

def certificate8 : RatMajorityCertificate := ⟨0,(1000048831422966257/1000000000000000000),(2724208969/2357590000),(43154921557573316341/100000000000000000000),(21577460778786658171/50000000000000000000),(68398978337488429/100000000000000000),false⟩
theorem valid8 : certificate8.Valid := by decide +kernel
theorem bound8 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate8.a certificate8.b certificate8.c x ≤ (certificate8.bound:ℝ) :=
  rat_majority_certificate_sound certificate8 valid8 x hx0 hx1

def certificate9 : RatMajorityCertificate := ⟨(205922045846601323/1000000000000000000),(794116730109846121645277229239441989/1000000000000000000000000000000000000),(2724208969/2357590000),(9654520556337832061/25000000000000000000),(7723616445070265649/20000000000000000000),(68398978337488429/100000000000000000),false⟩
theorem valid9 : certificate9.Valid := by decide +kernel
theorem bound9 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate9.a certificate9.b certificate9.c x ≤ (certificate9.bound:ℝ) :=
  rat_majority_certificate_sound certificate9 valid9 x hx0 hx1

def certificate10 : RatMajorityCertificate := ⟨0,(1000048831422966257/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(26988082684439061/50000000000000000),false⟩
theorem valid10 : certificate10.Valid := by decide +kernel
theorem bound10 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate10.a certificate10.b certificate10.c x ≤ (certificate10.bound:ℝ) :=
  rat_majority_certificate_sound certificate10 valid10 x hx0 hx1

def certificate11 : RatMajorityCertificate := ⟨(31244856574344031/250000000000000000),(218765825550590631420870101977638033/250000000000000000000000000000000000),1,(18308138922358071209/50000000000000000000),(36616277844716142419/100000000000000000000),(26988082684439061/50000000000000000),false⟩
theorem valid11 : certificate11.Valid := by decide +kernel
theorem bound11 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate11.a certificate11.b certificate11.c x ≤ (certificate11.bound:ℝ) :=
  rat_majority_certificate_sound certificate11 valid11 x hx0 hx1

def certificate12 : RatMajorityCertificate := ⟨0,(1000076187672614857/1000000000000000000),(677976413/585897500),(43193570594978617893/100000000000000000000),(21596785297489308947/50000000000000000000),(685444797203885443/1000000000000000000),false⟩
theorem valid12 : certificate12.Valid := by decide +kernel
theorem bound12 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate12.a certificate12.b certificate12.c x ≤ (certificate12.bound:ℝ) :=
  rat_majority_certificate_sound certificate12 valid12 x hx0 hx1

def certificate13 : RatMajorityCertificate := ⟨(20564803452803487/100000000000000000),(79441248529945147627095407342393641/100000000000000000000000000000000000),(677976413/585897500),(38665597254625482651/100000000000000000000),(9666399313656370663/25000000000000000000),(685444797203885443/1000000000000000000),false⟩
theorem valid13 : certificate13.Valid := by decide +kernel
theorem bound13 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate13.a certificate13.b certificate13.c x ≤ (certificate13.bound:ℝ) :=
  rat_majority_certificate_sound certificate13 valid13 x hx0 hx1

def certificate14 : RatMajorityCertificate := ⟨0,(1000076187672614857/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(539724554264025111/1000000000000000000),false⟩
theorem valid14 : certificate14.Valid := by decide +kernel
theorem bound14 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate14.a certificate14.b certificate14.c x ≤ (certificate14.bound:ℝ) :=
  rat_majority_certificate_sound certificate14 valid14 x hx0 hx1

def certificate15 : RatMajorityCertificate := ⟨(31129211559775413/250000000000000000),(218887463696199226458808682632889059/250000000000000000000000000000000000),1,(3662711917258955371/10000000000000000000),(36627119172589553711/100000000000000000000),(539724554264025111/1000000000000000000),false⟩
theorem valid15 : certificate15.Valid := by decide +kernel
theorem bound15 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate15.a certificate15.b certificate15.c x ≤ (certificate15.bound:ℝ) :=
  rat_majority_certificate_sound certificate15 valid15 x hx0 hx1

def certificate16 : RatMajorityCertificate := ⟨0,(1000109545884520517/1000000000000000000),(2700025271/2329650000),(10809040129736071611/25000000000000000000),(8647232103788857289/20000000000000000000),(343577777257066661/500000000000000000),false⟩
theorem valid16 : certificate16.Valid := by decide +kernel
theorem bound16 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate16.a certificate16.b certificate16.c x ≤ (certificate16.bound:ℝ) :=
  rat_majority_certificate_sound certificate16 valid16 x hx0 hx1

def certificate17 : RatMajorityCertificate := ⟨(206299298873256143/1000000000000000000),(793787647772093340659705023920214069/1000000000000000000000000000000000000),(2700025271/2329650000),(38692746465415580629/100000000000000000000),(3869274646541558063/10000000000000000000),(343577777257066661/500000000000000000),false⟩
theorem valid17 : certificate17.Valid := by decide +kernel
theorem bound17 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate17.a certificate17.b certificate17.c x ≤ (certificate17.bound:ℝ) :=
  rat_majority_certificate_sound certificate17 valid17 x hx0 hx1

def certificate18 : RatMajorityCertificate := ⟨0,(1000109545884520517/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(134945287418778513/250000000000000000),false⟩
theorem valid18 : certificate18.Valid := by decide +kernel
theorem bound18 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate18.a certificate18.b certificate18.c x ≤ (certificate18.bound:ℝ) :=
  rat_majority_certificate_sound certificate18 valid18 x hx0 hx1

def certificate19 : RatMajorityCertificate := ⟨(124900664410254657/1000000000000000000),(875195199120505838395796985688702331/1000000000000000000000000000000000000),1,(36618267128384116951/100000000000000000000),(4577283391048014619/12500000000000000000),(134945287418778513/250000000000000000),false⟩
theorem valid19 : certificate19.Valid := by decide +kernel
theorem bound19 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate19.a certificate19.b certificate19.c x ≤ (certificate19.bound:ℝ) :=
  rat_majority_certificate_sound certificate19 valid19 x hx0 hx1

def certificate20 : RatMajorityCertificate := ⟨0,(100014884607633889/100000000000000000),(2688640631/2316220000),(10819554977450304137/25000000000000000000),(43278219909801216549/100000000000000000000),(344422186976356671/500000000000000000),false⟩
theorem valid20 : certificate20.Valid := by decide +kernel
theorem bound20 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate20.a certificate20.b certificate20.c x ≤ (certificate20.bound:ℝ) :=
  rat_majority_certificate_sound certificate20 valid20 x hx0 hx1

def certificate21 : RatMajorityCertificate := ⟨(206872344468827847/1000000000000000000),(79324570947073383070183748055893017/100000000000000000000000000000000000),(2688640631/2316220000),(19360721050879587133/50000000000000000000),(38721442101759174267/100000000000000000000),(344422186976356671/500000000000000000),false⟩
theorem valid21 : certificate21.Valid := by decide +kernel
theorem bound21 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate21.a certificate21.b certificate21.c x ≤ (certificate21.bound:ℝ) :=
  rat_majority_certificate_sound certificate21 valid21 x hx0 hx1

def certificate22 : RatMajorityCertificate := ⟨0,(100014884607633889/100000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(269864943018699869/500000000000000000),false⟩
theorem valid22 : certificate22.Valid := by decide +kernel
theorem bound22 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate22.a certificate22.b certificate22.c x ≤ (certificate22.bound:ℝ) :=
  rat_majority_certificate_sound certificate22 valid22 x hx0 hx1

def certificate23 : RatMajorityCertificate := ⟨(124254516139088079/1000000000000000000),(87587583514005612045624809643690769/100000000000000000000000000000000000),1,(36633407755144124173/100000000000000000000),(18316703877572062087/50000000000000000000),(269864943018699869/500000000000000000),false⟩
theorem valid23 : certificate23.Valid := by decide +kernel
theorem bound23 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate23.a certificate23.b certificate23.c x ≤ (certificate23.bound:ℝ) :=
  rat_majority_certificate_sound certificate23 valid23 x hx0 hx1

def certificate24 : RatMajorityCertificate := ⟨0,(1000194032136813037/1000000000000000000),(2677761569/2303260000),(43320283927679338417/100000000000000000000),(21660141963839669209/50000000000000000000),(345272913233724549/500000000000000000),false⟩
theorem valid24 : certificate24.Valid := by decide +kernel
theorem bound24 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate24.a certificate24.b certificate24.c x ≤ (certificate24.bound:ℝ) :=
  rat_majority_certificate_sound certificate24 valid24 x hx0 hx1

def certificate25 : RatMajorityCertificate := ⟨(41499983436050141/200000000000000000),(158530770660848663949705772925511783/200000000000000000000000000000000000),(2677761569/2303260000),(7749744742439725669/20000000000000000000),(19374361856099314173/50000000000000000000),(345272913233724549/500000000000000000),false⟩
theorem valid25 : certificate25.Valid := by decide +kernel
theorem bound25 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate25.a certificate25.b certificate25.c x ≤ (certificate25.bound:ℝ) :=
  rat_majority_certificate_sound certificate25 valid25 x hx0 hx1

def certificate26 : RatMajorityCertificate := ⟨0,(1000194032136813037/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(2698830513645927/5000000000000000),false⟩
theorem valid26 : certificate26.Valid := by decide +kernel
theorem bound26 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate26.a certificate26.b certificate26.c x ≤ (certificate26.bound:ℝ) :=
  rat_majority_certificate_sound certificate26 valid26 x hx0 hx1

def certificate27 : RatMajorityCertificate := ⟨(12439799519552507/100000000000000000),(87577189973246492136020656636366241/100000000000000000000000000000000000),1,(366301839558087133/1000000000000000000),(36630183955808713301/100000000000000000000),(2698830513645927/5000000000000000),false⟩
theorem valid27 : certificate27.Valid := by decide +kernel
theorem bound27 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate27.a certificate27.b certificate27.c x ≤ (certificate27.bound:ℝ) :=
  rat_majority_certificate_sound certificate27 valid27 x hx0 hx1

def certificate28 : RatMajorityCertificate := ⟨0,(1000245044783335231/1000000000000000000),(889098753/763570000),(346896842334009197/800000000000000000),(21681052645875574813/50000000000000000000),(692241387556439571/1000000000000000000),false⟩
theorem valid28 : certificate28.Valid := by decide +kernel
theorem bound28 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate28.a certificate28.b certificate28.c x ≤ (certificate28.bound:ℝ) :=
  rat_majority_certificate_sound certificate28 valid28 x hx0 hx1

def certificate29 : RatMajorityCertificate := ⟨(41619510972545701/200000000000000000),(158419299340072559469458034649108069/200000000000000000000000000000000000),(889098753/763570000),(19388286551441642031/50000000000000000000),(38776573102883284063/100000000000000000000),(692241387556439571/1000000000000000000),false⟩
theorem valid29 : certificate29.Valid := by decide +kernel
theorem bound29 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate29.a certificate29.b certificate29.c x ≤ (certificate29.bound:ℝ) :=
  rat_majority_certificate_sound certificate29 valid29 x hx0 hx1

def certificate30 : RatMajorityCertificate := ⟨0,(1000245044783335231/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(539793581540657223/1000000000000000000),false⟩
theorem valid30 : certificate30.Valid := by decide +kernel
theorem bound30 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate30.a certificate30.b certificate30.c x ≤ (certificate30.bound:ℝ) :=
  rat_majority_certificate_sound certificate30 valid30 x hx0 hx1

def certificate31 : RatMajorityCertificate := ⟨(124435008724123123/1000000000000000000),(875779543909459987670049586172353587/1000000000000000000000000000000000000),1,(18314725983831059229/50000000000000000000),(36629451967662118459/100000000000000000000),(539793581540657223/1000000000000000000),false⟩
theorem valid31 : certificate31.Valid := by decide +kernel
theorem bound31 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate31.a certificate31.b certificate31.c x ≤ (certificate31.bound:ℝ) :=
  rat_majority_certificate_sound certificate31 valid31 x hx0 hx1

def certificate32 : RatMajorityCertificate := ⟨0,(1000301818480832519/1000000000000000000),(2657183821/2278540000),(43403396408284239671/100000000000000000000),(5425424551035529959/12500000000000000000),(346955590092396669/500000000000000000),false⟩
theorem valid32 : certificate32.Valid := by decide +kernel
theorem bound32 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate32.a certificate32.b certificate32.c x ≤ (certificate32.bound:ℝ) :=
  rat_majority_certificate_sound certificate32 valid32 x hx0 hx1

def certificate33 : RatMajorityCertificate := ⟨(52145760456150941/250000000000000000),(197913955609854456829987615994749621/250000000000000000000000000000000000),(2657183821/2278540000),(9701719291390606347/25000000000000000000),(38806877165562425389/100000000000000000000),(346955590092396669/500000000000000000),false⟩
theorem valid33 : certificate33.Valid := by decide +kernel
theorem bound33 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate33.a certificate33.b certificate33.c x ≤ (certificate33.bound:ℝ) :=
  rat_majority_certificate_sound certificate33 valid33 x hx0 hx1

def certificate34 : RatMajorityCertificate := ⟨0,(1000301818480832519/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(269911287958720621/500000000000000000),false⟩
theorem valid34 : certificate34.Valid := by decide +kernel
theorem bound34 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate34.a certificate34.b certificate34.c x ≤ (certificate34.bound:ℝ) :=
  rat_majority_certificate_sound certificate34 valid34 x hx0 hx1

def certificate35 : RatMajorityCertificate := ⟨(124461415395373259/1000000000000000000),(875802838330142363350852432929790579/1000000000000000000000000000000000000),1,(36628981412338917403/100000000000000000000),(9157245353084729351/25000000000000000000),(269911287958720621/500000000000000000),false⟩
theorem valid35 : certificate35.Valid := by decide +kernel
theorem bound35 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate35.a certificate35.b certificate35.c x ≤ (certificate35.bound:ℝ) :=
  rat_majority_certificate_sound certificate35 valid35 x hx0 hx1

def certificate36 : RatMajorityCertificate := ⟨0,(1000364280379285999/1000000000000000000),(882499253/755580000),(43445000614263694733/100000000000000000000),(21722500307131847367/50000000000000000000),(695611327831907727/1000000000000000000),false⟩
theorem valid36 : certificate36.Valid := by decide +kernel
theorem bound36 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate36.a certificate36.b certificate36.c x ≤ (certificate36.bound:ℝ) :=
  rat_majority_certificate_sound certificate36 valid36 x hx0 hx1

def certificate37 : RatMajorityCertificate := ⟨(104589617824653929/500000000000000000),(395554422419338527885091807709959929/500000000000000000000000000000000000),(882499253/755580000),(38834594165700029419/100000000000000000000),(1941729708285001471/5000000000000000000),(695611327831907727/1000000000000000000),false⟩
theorem valid37 : certificate37.Valid := by decide +kernel
theorem bound37 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate37.a certificate37.b certificate37.c x ≤ (certificate37.bound:ℝ) :=
  rat_majority_certificate_sound certificate37 valid37 x hx0 hx1

def certificate38 : RatMajorityCertificate := ⟨0,(1000364280379285999/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(53985425427305963/100000000000000000),false⟩
theorem valid38 : certificate38.Valid := by decide +kernel
theorem bound38 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate38.a certificate38.b certificate38.c x ≤ (certificate38.bound:ℝ) :=
  rat_majority_certificate_sound certificate38 valid38 x hx0 hx1

def certificate39 : RatMajorityCertificate := ⟨(124488422262078077/1000000000000000000),(875830509427529576596504316749056077/1000000000000000000000000000000000000),1,(9157127833208102351/25000000000000000000),(7325702266566481881/20000000000000000000),(53985425427305963/100000000000000000),false⟩
theorem valid39 : certificate39.Valid := by decide +kernel
theorem bound39 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate39.a certificate39.b certificate39.c x ≤ (certificate39.bound:ℝ) :=
  rat_majority_certificate_sound certificate39 valid39 x hx0 hx1

end Cycle12.MajorityCertificates.Batch000
