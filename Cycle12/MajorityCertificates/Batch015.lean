import Cycle12.RationalMajorityCertificate

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MajorityCertificates.Batch015

def certificate600 : RatMajorityCertificate := ⟨0,(504353208116021683/500000000000000000),(1131026219/971400000),(10840113084291958707/25000000000000000000),(43360452337167834829/100000000000000000000),(693875006136212573/1000000000000000000),false⟩
theorem valid600 : certificate600.Valid := by decide +kernel
theorem bound600 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate600.a certificate600.b certificate600.c x ≤ (certificate600.bound:ℝ) :=
  rat_majority_certificate_sound certificate600 valid600 x hx0 hx1

def certificate601 : RatMajorityCertificate := ⟨(35788409929210627/200000000000000000),(82820642262035672412977656193974759/100000000000000000000000000000000000),(1131026219/971400000),(19779026191793494513/50000000000000000000),(39558052383586989027/100000000000000000000),(693875006136212573/1000000000000000000),false⟩
theorem valid601 : certificate601.Valid := by decide +kernel
theorem bound601 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate601.a certificate601.b certificate601.c x ≤ (certificate601.bound:ℝ) :=
  rat_majority_certificate_sound certificate601 valid601 x hx0 hx1

def certificate602 : RatMajorityCertificate := ⟨0,(504353208116021683/500000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(21727152529529763/40000000000000000),false⟩
theorem valid602 : certificate602.Valid := by decide +kernel
theorem bound602 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate602.a certificate602.b certificate602.c x ≤ (certificate602.bound:ℝ) :=
  rat_majority_certificate_sound certificate602 valid602 x hx0 hx1

def certificate603 : RatMajorityCertificate := ⟨(119389923397859551/1000000000000000000),(444138517233585138273849648295355667/500000000000000000000000000000000000),1,(36766663437150063127/100000000000000000000),(4595832929643757891/12500000000000000000),(21727152529529763/40000000000000000),false⟩
theorem valid603 : certificate603.Valid := by decide +kernel
theorem bound603 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate603.a certificate603.b certificate603.c x ≤ (certificate603.bound:ℝ) :=
  rat_majority_certificate_sound certificate603 valid603 x hx0 hx1

def certificate604 : RatMajorityCertificate := ⟨0,(504363463625543843/500000000000000000),(565316349/485642500),(8670849803864648137/20000000000000000000),(21677124509661620343/50000000000000000000),(693665104602796187/1000000000000000000),false⟩
theorem valid604 : certificate604.Valid := by decide +kernel
theorem bound604 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate604.a certificate604.b certificate604.c x ≤ (certificate604.bound:ℝ) :=
  rat_majority_certificate_sound certificate604 valid604 x hx0 hx1

def certificate605 : RatMajorityCertificate := ⟨(44790432542544553/250000000000000000),(103500208211941915864837380317662821/125000000000000000000000000000000000),(565316349/485642500),(39546247133497214261/100000000000000000000),(19773123566748607131/50000000000000000000),(693665104602796187/1000000000000000000),false⟩
theorem valid605 : certificate605.Valid := by decide +kernel
theorem bound605 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate605.a certificate605.b certificate605.c x ≤ (certificate605.bound:ℝ) :=
  rat_majority_certificate_sound certificate605 valid605 x hx0 hx1

def certificate606 : RatMajorityCertificate := ⟨0,(504363463625543843/500000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(54317339580174863/100000000000000000),false⟩
theorem valid606 : certificate606.Valid := by decide +kernel
theorem bound606 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate606.a certificate606.b certificate606.c x ≤ (certificate606.bound:ℝ) :=
  rat_majority_certificate_sound certificate606 valid606 x hx0 hx1

def certificate607 : RatMajorityCertificate := ⟨(119242436622629549/1000000000000000000),(444221935279405007446628184153183193/500000000000000000000000000000000000),1,(18385042994168264211/50000000000000000000),(36770085988336528423/100000000000000000000),(54317339580174863/100000000000000000),false⟩
theorem valid607 : certificate607.Valid := by decide +kernel
theorem bound607 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate607.a certificate607.b certificate607.c x ≤ (certificate607.bound:ℝ) :=
  rat_majority_certificate_sound certificate607 valid607 x hx0 hx1

def certificate608 : RatMajorityCertificate := ⟨0,(1008747448405069081/1000000000000000000),(564984709/485582500),(43341732173354056197/100000000000000000000),(21670866086677028099/50000000000000000000),(138613867834410973/200000000000000000),false⟩
theorem valid608 : certificate608.Valid := by decide +kernel
theorem bound608 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate608.a certificate608.b certificate608.c x ≤ (certificate608.bound:ℝ) :=
  rat_majority_certificate_sound certificate608 valid608 x hx0 hx1

def certificate609 : RatMajorityCertificate := ⟨(2222995171226833/12500000000000000),(10366902398271506083551525114149527/12500000000000000000000000000000000),(564984709/485582500),(39566254971725890301/100000000000000000000),(19783127485862945151/50000000000000000000),(138613867834410973/200000000000000000),false⟩
theorem valid609 : certificate609.Valid := by decide +kernel
theorem bound609 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate609.a certificate609.b certificate609.c x ≤ (certificate609.bound:ℝ) :=
  rat_majority_certificate_sound certificate609 valid609 x hx0 hx1

def certificate610 : RatMajorityCertificate := ⟨0,(1008747448405069081/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(108633607960502669/200000000000000000),false⟩
theorem valid610 : certificate610.Valid := by decide +kernel
theorem bound610 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate610.a certificate610.b certificate610.c x ≤ (certificate610.bound:ℝ) :=
  rat_majority_certificate_sound certificate610 valid610 x hx0 hx1

def certificate611 : RatMajorityCertificate := ⟨(119095421831920221/1000000000000000000),(888610245515394200053890731614213099/1000000000000000000000000000000000000),1,(36773496754417755297/100000000000000000000),(18386748377208877649/50000000000000000000),(108633607960502669/200000000000000000),false⟩
theorem valid611 : certificate611.Valid := by decide +kernel
theorem bound611 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate611.a certificate611.b certificate611.c x ≤ (certificate611.bound:ℝ) :=
  rat_majority_certificate_sound certificate611 valid611 x hx0 hx1

def certificate612 : RatMajorityCertificate := ⟨0,(100876784339938333/100000000000000000),(1129491679/971055000),(43333366574697470311/100000000000000000000),(5416670821837183789/12500000000000000000),(10823863103524857/15625000000000000),false⟩
theorem valid612 : certificate612.Valid := by decide +kernel
theorem bound612 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate612.a certificate612.b certificate612.c x ≤ (certificate612.bound:ℝ) :=
  rat_majority_certificate_sound certificate612 valid612 x hx0 hx1

def certificate613 : RatMajorityCertificate := ⟨(177528856692024241/1000000000000000000),(82968244149301185514596441118869747/100000000000000000000000000000000000),(1129491679/971055000),(39565398125993940147/100000000000000000000),(9891349531498485037/25000000000000000000),(10823863103524857/15625000000000000),false⟩
theorem valid613 : certificate613.Valid := by decide +kernel
theorem bound613 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate613.a certificate613.b certificate613.c x ≤ (certificate613.bound:ℝ) :=
  rat_majority_certificate_sound certificate613 valid613 x hx0 hx1

def certificate614 : RatMajorityCertificate := ⟨0,(100876784339938333/100000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(543166554658378463/1000000000000000000),false⟩
theorem valid614 : certificate614.Valid := by decide +kernel
theorem bound614 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate614.a certificate614.b certificate614.c x ≤ (certificate614.bound:ℝ) :=
  rat_majority_certificate_sound certificate614 valid614 x hx0 hx1

def certificate615 : RatMajorityCertificate := ⟨(118987185460817917/1000000000000000000),(88873739692991158049548792478487639/100000000000000000000000000000000000),1,(3677601976802355391/10000000000000000000),(36776019768023553911/100000000000000000000),(543166554658378463/1000000000000000000),false⟩
theorem valid615 : certificate615.Valid := by decide +kernel
theorem bound615 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate615.a certificate615.b certificate615.c x ≤ (certificate615.bound:ℝ) :=
  rat_majority_certificate_sound certificate615 valid615 x hx0 hx1

def certificate616 : RatMajorityCertificate := ⟨0,(1008788247989916963/1000000000000000000),(28227587/24273500),(8665455656170307299/20000000000000000000),(2707954892553221031/6250000000000000000),(43282796655331063/62500000000000000),false⟩
theorem valid616 : certificate616.Valid := by decide +kernel
theorem bound616 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate616.a certificate616.b certificate616.c x ≤ (certificate616.bound:ℝ) :=
  rat_majority_certificate_sound certificate616 valid616 x hx0 hx1

def certificate617 : RatMajorityCertificate := ⟨(177779062216485843/1000000000000000000),(829446819287257765585381064764945191/1000000000000000000000000000000000000),(28227587/24273500),(39552969212515567611/100000000000000000000),(9888242303128891903/25000000000000000000),(43282796655331063/62500000000000000),false⟩
theorem valid617 : certificate617.Valid := by decide +kernel
theorem bound617 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate617.a certificate617.b certificate617.c x ≤ (certificate617.bound:ℝ) :=
  rat_majority_certificate_sound certificate617 valid617 x hx0 hx1

def certificate618 : RatMajorityCertificate := ⟨0,(1008788247989916963/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(271580626192399747/500000000000000000),false⟩
theorem valid618 : certificate618.Valid := by decide +kernel
theorem bound618 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate618.a certificate618.b certificate618.c x ≤ (certificate618.bound:ℝ) :=
  rat_majority_certificate_sound certificate618 valid618 x hx0 hx1

def certificate619 : RatMajorityCertificate := ⟨(14855134931465801/125000000000000000),(111112845457572419787447314135717637/125000000000000000000000000000000000),1,(4597425964562868171/12500000000000000000),(36779407716502945369/100000000000000000000),(271580626192399747/500000000000000000),false⟩
theorem valid619 : certificate619.Valid := by decide +kernel
theorem bound619 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate619.a certificate619.b certificate619.c x ≤ (certificate619.bound:ℝ) :=
  rat_majority_certificate_sound certificate619 valid619 x hx0 hx1

def certificate620 : RatMajorityCertificate := ⟨0,(1008808616566238077/1000000000000000000),(2257187933/1941650000),(10829570630546777329/25000000000000000000),(43318282522187109317/100000000000000000000),(346072232936335609/500000000000000000),false⟩
theorem valid620 : certificate620.Valid := by decide +kernel
theorem bound620 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate620.a certificate620.b certificate620.c x ≤ (certificate620.bound:ℝ) :=
  rat_majority_certificate_sound certificate620 valid620 x hx0 hx1

def certificate621 : RatMajorityCertificate := ⟨(35463066675238897/200000000000000000),(165986276081403603569353391447118931/200000000000000000000000000000000000),(2257187933/1941650000),(7911051440312708103/20000000000000000000),(9888814300390885129/25000000000000000000),(346072232936335609/500000000000000000),false⟩
theorem valid621 : certificate621.Valid := by decide +kernel
theorem bound621 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate621.a certificate621.b certificate621.c x ≤ (certificate621.bound:ℝ) :=
  rat_majority_certificate_sound certificate621 valid621 x hx0 hx1

def certificate622 : RatMajorityCertificate := ⟨0,(1008808616566238077/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(271577997255698149/500000000000000000),false⟩
theorem valid622 : certificate622.Valid := by decide +kernel
theorem bound622 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate622.a certificate622.b certificate622.c x ≤ (certificate622.bound:ℝ) :=
  rat_majority_certificate_sound certificate622 valid622 x hx0 hx1

def certificate623 : RatMajorityCertificate := ⟨(14836936373159531/125000000000000000),(111133447814091395289171696752338113/125000000000000000000000000000000000),1,(9195695689352417247/25000000000000000000),(36782782757409668989/100000000000000000000),(271577997255698149/500000000000000000),false⟩
theorem valid623 : certificate623.Valid := by decide +kernel
theorem bound623 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate623.a certificate623.b certificate623.c x ≤ (certificate623.bound:ℝ) :=
  rat_majority_certificate_sound certificate623 valid623 x hx0 hx1

def certificate624 : RatMajorityCertificate := ⟨0,(1008828903071547729/1000000000000000000),(90245891/77657200),(43308883022450872197/100000000000000000000),(21654441511225436099/50000000000000000000),(172935092445179733/250000000000000000),false⟩
theorem valid624 : certificate624.Valid := by decide +kernel
theorem bound624 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate624.a certificate624.b certificate624.c x ≤ (certificate624.bound:ℝ) :=
  rat_majority_certificate_sound certificate624 valid624 x hx0 hx1

def certificate625 : RatMajorityCertificate := ⟨(176760485949369323/1000000000000000000),(830507815924851749989443546957082533/1000000000000000000000000000000000000),(90245891/77657200),(7911875529522085149/20000000000000000000),(19779688823805212873/50000000000000000000),(172935092445179733/250000000000000000),false⟩
theorem valid625 : certificate625.Valid := by decide +kernel
theorem bound625 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate625.a certificate625.b certificate625.c x ≤ (certificate625.bound:ℝ) :=
  rat_majority_certificate_sound certificate625 valid625 x hx0 hx1

def certificate626 : RatMajorityCertificate := ⟨0,(1008828903071547729/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(543150674906234341/1000000000000000000),false⟩
theorem valid626 : certificate626.Valid := by decide +kernel
theorem bound626 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate626.a certificate626.b certificate626.c x ≤ (certificate626.bound:ℝ) :=
  rat_majority_certificate_sound certificate626 valid626 x hx0 hx1

def certificate627 : RatMajorityCertificate := ⟨(29637395347716421/250000000000000000),(222308164729352383366879561741442091/250000000000000000000000000000000000),1,(73572327896714964153261/200000000000000000000000),(183930819741787410383153/500000000000000000000000),(543150674906234341/1000000000000000000),false⟩
theorem valid627 : certificate627.Valid := by decide +kernel
theorem bound627 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate627.a certificate627.b certificate627.c x ≤ (certificate627.bound:ℝ) :=
  rat_majority_certificate_sound certificate627 valid627 x hx0 hx1

def certificate628 : RatMajorityCertificate := ⟨0,(252212288201007861/250000000000000000),(751623467/647070000),(2706040429403447531/6250000000000000000),(43296646870455160497/100000000000000000000),(43201366783117419/62500000000000000),false⟩
theorem valid628 : certificate628.Valid := by decide +kernel
theorem bound628 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate628.a certificate628.b certificate628.c x ≤ (certificate628.bound:ℝ) :=
  rat_majority_certificate_sound certificate628 valid628 x hx0 hx1

def certificate629 : RatMajorityCertificate := ⟨(88077719388036843/500000000000000000),(103891860954120884522725701199377177/125000000000000000000000000000000000),(751623467/647070000),(9890449538249170001/25000000000000000000),(7912359630599336001/20000000000000000000),(43201366783117419/62500000000000000),false⟩
theorem valid629 : certificate629.Valid := by decide +kernel
theorem bound629 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate629.a certificate629.b certificate629.c x ≤ (certificate629.bound:ℝ) :=
  rat_majority_certificate_sound certificate629 valid629 x hx0 hx1

def certificate630 : RatMajorityCertificate := ⟨0,(252212288201007861/250000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(265206320948599/488281250000000),false⟩
theorem valid630 : certificate630.Valid := by decide +kernel
theorem bound630 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate630.a certificate630.b certificate630.c x ≤ (certificate630.bound:ℝ) :=
  rat_majority_certificate_sound certificate630 valid630 x hx0 hx1

def certificate631 : RatMajorityCertificate := ⟨(4735036216226301/40000000000000000),(8894257209231236837432129744047839/10000000000000000000000000000000000),1,(9197544518564477503/25000000000000000000),(36790178074257910013/100000000000000000000),(265206320948599/488281250000000),false⟩
theorem valid631 : certificate631.Valid := by decide +kernel
theorem bound631 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate631.a certificate631.b certificate631.c x ≤ (certificate631.bound:ℝ) :=
  rat_majority_certificate_sound certificate631 valid631 x hx0 hx1

def certificate632 : RatMajorityCertificate := ⟨0,(1008869365496675817/1000000000000000000),(2253912731/1940990000),(2705514344546140639/6250000000000000000),(1731529180509530009/4000000000000000000),(43179121045838453/62500000000000000),false⟩
theorem valid632 : certificate632.Valid := by decide +kernel
theorem bound632 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate632.a certificate632.b certificate632.c x ≤ (certificate632.bound:ℝ) :=
  rat_majority_certificate_sound certificate632 valid632 x hx0 hx1

def certificate633 : RatMajorityCertificate := ⟨(878536175538911/5000000000000000),(4158018593501561738888640963784713/5000000000000000000000000000000000),(2253912731/1940990000),(19782134239437708521/50000000000000000000),(39564268478875417043/100000000000000000000),(43179121045838453/62500000000000000),false⟩
theorem valid633 : certificate633.Valid := by decide +kernel
theorem bound633 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate633.a certificate633.b certificate633.c x ≤ (certificate633.bound:ℝ) :=
  rat_majority_certificate_sound certificate633 valid633 x hx0 hx1

def certificate634 : RatMajorityCertificate := ⟨0,(1008869365496675817/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(543141286275224849/1000000000000000000),false⟩
theorem valid634 : certificate634.Valid := by decide +kernel
theorem bound634 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate634.a certificate634.b certificate634.c x ≤ (certificate634.bound:ℝ) :=
  rat_majority_certificate_sound certificate634 valid634 x hx0 hx1

def certificate635 : RatMajorityCertificate := ⟨(59135204455651777/500000000000000000),(444774986550648303590415508391023191/500000000000000000000000000000000000),1,(919815859611560323/2500000000000000000),(36792634384462412921/100000000000000000000),(543141286275224849/1000000000000000000),false⟩
theorem valid635 : certificate635.Valid := by decide +kernel
theorem bound635 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate635.a certificate635.b certificate635.c x ≤ (certificate635.bound:ℝ) :=
  rat_majority_certificate_sound certificate635 valid635 x hx0 hx1

def certificate636 : RatMajorityCertificate := ⟨0,(504444770441448463/500000000000000000),(450626349/388154000),(21640963374749984937/50000000000000000000),(346255413995999759/800000000000000000),(690662151290239921/1000000000000000000),false⟩
theorem valid636 : certificate636.Valid := by decide +kernel
theorem bound636 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate636.a certificate636.b certificate636.c x ≤ (certificate636.bound:ℝ) :=
  rat_majority_certificate_sound certificate636 valid636 x hx0 hx1

def certificate637 : RatMajorityCertificate := ⟨(35206345009352487/200000000000000000),(83129297461964442554130633988622519/100000000000000000000000000000000000),(450626349/388154000),(395498011008907032619347/1000000000000000000000000),(98874502752226758154837/250000000000000000000000),(690662151290239921/1000000000000000000),false⟩
theorem valid637 : certificate637.Valid := by decide +kernel
theorem bound637 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate637.a certificate637.b certificate637.c x ≤ (certificate637.bound:ℝ) :=
  rat_majority_certificate_sound certificate637 valid637 x hx0 hx1

def certificate638 : RatMajorityCertificate := ⟨0,(504444770441448463/500000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(543136110427771117/1000000000000000000),false⟩
theorem valid638 : certificate638.Valid := by decide +kernel
theorem bound638 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate638.a certificate638.b certificate638.c x ≤ (certificate638.bound:ℝ) :=
  rat_majority_certificate_sound certificate638 valid638 x hx0 hx1

def certificate639 : RatMajorityCertificate := ⟨(118126181753002423/1000000000000000000),(444856635803930337545400724731374151/500000000000000000000000000000000000),1,(36795974017093323277/100000000000000000000),(18397987008546661639/50000000000000000000),(543136110427771117/1000000000000000000),false⟩
theorem valid639 : certificate639.Valid := by decide +kernel
theorem bound639 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate639.a certificate639.b certificate639.c x ≤ (certificate639.bound:ℝ) :=
  rat_majority_certificate_sound certificate639 valid639 x hx0 hx1

end Cycle12.MajorityCertificates.Batch015
