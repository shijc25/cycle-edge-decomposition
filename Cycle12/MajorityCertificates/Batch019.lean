import Cycle12.RationalMajorityCertificate

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MajorityCertificates.Batch019

def certificate760 : RatMajorityCertificate := ⟨0,(250247864944575197/250000000000000000),(16296159/13741250),(21928303342793172157/50000000000000000000),(8771321337117268863/20000000000000000000),(2845966391142649/4000000000000000),false⟩
theorem valid760 : certificate760.Valid := by decide +kernel
theorem bound760 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate760.a certificate760.b certificate760.c x ≤ (certificate760.bound:ℝ) :=
  rat_majority_certificate_sound certificate760 valid760 x hx0 hx1

def certificate761 : RatMajorityCertificate := ⟨(204026769074007201/1000000000000000000),(199190601592265011437777476536006403/250000000000000000000000000000000000),(16296159/13741250),(39401834880081737381/100000000000000000000),(19700917440040868691/50000000000000000000),(2845966391142649/4000000000000000),false⟩
theorem valid761 : certificate761.Valid := by decide +kernel
theorem bound761 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate761.a certificate761.b certificate761.c x ≤ (certificate761.bound:ℝ) :=
  rat_majority_certificate_sound certificate761 valid761 x hx0 hx1

def certificate762 : RatMajorityCertificate := ⟨0,(250247864944575197/250000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(540882845335342503/1000000000000000000),false⟩
theorem valid762 : certificate762.Valid := by decide +kernel
theorem bound762 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate762.a certificate762.b certificate762.c x ≤ (certificate762.bound:ℝ) :=
  rat_majority_certificate_sound certificate762 valid762 x hx0 hx1

def certificate763 : RatMajorityCertificate := ⟨(13135070440018017/100000000000000000),(21737763160946409075745416908675651/25000000000000000000000000000000000),1,(36469532844373510413/100000000000000000000),(18234766422186755207/50000000000000000000),(540882845335342503/1000000000000000000),false⟩
theorem valid763 : certificate763.Valid := by decide +kernel
theorem bound763 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate763.a certificate763.b certificate763.c x ≤ (certificate763.bound:ℝ) :=
  rat_majority_certificate_sound certificate763 valid763 x hx0 hx1

def certificate764 : RatMajorityCertificate := ⟨0,(20021193435243843/20000000000000000),(650154533/548225000),(2741033054460901421/6250000000000000000),(43856528871374422737/100000000000000000000),(711195297471065987/1000000000000000000),false⟩
theorem valid764 : certificate764.Valid := by decide +kernel
theorem bound764 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate764.a certificate764.b certificate764.c x ≤ (certificate764.bound:ℝ) :=
  rat_majority_certificate_sound certificate764 valid764 x hx0 hx1

def certificate765 : RatMajorityCertificate := ⟨(200734377994137651/1000000000000000000),(16002251624319858120379254307767207/20000000000000000000000000000000000),(650154533/548225000),(7897611444426040849/20000000000000000000),(19744028611065102123/50000000000000000000),(711195297471065987/1000000000000000000),false⟩
theorem valid765 : certificate765.Valid := by decide +kernel
theorem bound765 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate765.a certificate765.b certificate765.c x ≤ (certificate765.bound:ℝ) :=
  rat_majority_certificate_sound certificate765 valid765 x hx0 hx1

def certificate766 : RatMajorityCertificate := ⟨0,(20021193435243843/20000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(108182797680497211/200000000000000000),false⟩
theorem valid766 : certificate766.Valid := by decide +kernel
theorem bound766 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate766.a certificate766.b certificate766.c x ≤ (certificate766.bound:ℝ) :=
  rat_majority_certificate_sound certificate766 valid766 x hx0 hx1

def certificate767 : RatMajorityCertificate := ⟨(32837610314884801/250000000000000000),(4347850210745493668025506110469757/5000000000000000000000000000000000),1,(7293944415344355263/20000000000000000000),(9117430519180444079/25000000000000000000),(108182797680497211/200000000000000000),false⟩
theorem valid767 : certificate767.Valid := by decide +kernel
theorem bound767 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate767.a certificate767.b certificate767.c x ≤ (certificate767.bound:ℝ) :=
  rat_majority_certificate_sound certificate767 valid767 x hx0 hx1

def certificate768 : RatMajorityCertificate := ⟨0,(1001129543072239339/1000000000000000000),(2595037939/2187340000),(43867058399746075531/100000000000000000000),(10966764599936518883/25000000000000000000),(711606056937455259/1000000000000000000),false⟩
theorem valid768 : certificate768.Valid := by decide +kernel
theorem bound768 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate768.a certificate768.b certificate768.c x ≤ (certificate768.bound:ℝ) :=
  rat_majority_certificate_sound certificate768 valid768 x hx0 hx1

def certificate769 : RatMajorityCertificate := ⟨(200288546335538107/1000000000000000000),(800614762196739037083454753941008727/1000000000000000000000000000000000000),(2595037939/2187340000),(4938863726169504963/12500000000000000000),(7902181961871207941/20000000000000000000),(711606056937455259/1000000000000000000),false⟩
theorem valid769 : certificate769.Valid := by decide +kernel
theorem bound769 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate769.a certificate769.b certificate769.c x ≤ (certificate769.bound:ℝ) :=
  rat_majority_certificate_sound certificate769 valid769 x hx0 hx1

def certificate770 : RatMajorityCertificate := ⟨0,(1001129543072239339/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(540850638160452761/1000000000000000000),false⟩
theorem valid770 : certificate770.Valid := by decide +kernel
theorem bound770 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate770.a certificate770.b certificate770.c x ≤ (certificate770.bound:ℝ) :=
  rat_majority_certificate_sound certificate770 valid770 x hx0 hx1

def certificate771 : RatMajorityCertificate := ⟨(130472312836609701/1000000000000000000),(870509856138546001731385457198772361/1000000000000000000000000000000000000),1,(9122641075845015013/25000000000000000000),(36490564303380060053/100000000000000000000),(540850638160452761/1000000000000000000),false⟩
theorem valid771 : certificate771.Valid := by decide +kernel
theorem bound771 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate771.a certificate771.b certificate771.c x ≤ (certificate771.bound:ℝ) :=
  rat_majority_certificate_sound certificate771 valid771 x hx0 hx1

def certificate772 : RatMajorityCertificate := ⟨0,(1001201007737049293/1000000000000000000),(647960739/545477500),(10975210958676728499/25000000000000000000),(43900843834706913997/100000000000000000000),(713054341547953739/1000000000000000000),false⟩
theorem valid772 : certificate772.Valid := by decide +kernel
theorem bound772 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate772.a certificate772.b certificate772.c x ≤ (certificate772.bound:ℝ) :=
  rat_majority_certificate_sound certificate772 valid772 x hx0 hx1

def certificate773 : RatMajorityCertificate := ⟨(20099324478835527/100000000000000000),(79996636850660856583320992361367589/100000000000000000000000000000000000),(647960739/545477500),(19764016090291839507/50000000000000000000),(7905606436116735803/20000000000000000000),(713054341547953739/1000000000000000000),false⟩
theorem valid773 : certificate773.Valid := by decide +kernel
theorem bound773 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate773.a certificate773.b certificate773.c x ≤ (certificate773.bound:ℝ) :=
  rat_majority_certificate_sound certificate773 valid773 x hx0 hx1

def certificate774 : RatMajorityCertificate := ⟨0,(1001201007737049293/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(540914279576251667/1000000000000000000),false⟩
theorem valid774 : certificate774.Valid := by decide +kernel
theorem bound774 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate774.a certificate774.b certificate774.c x ≤ (certificate774.bound:ℝ) :=
  rat_majority_certificate_sound certificate774 valid774 x hx0 hx1

def certificate775 : RatMajorityCertificate := ⟨(26151571391455553/200000000000000000),(174057221916377170535746787420425971/200000000000000000000000000000000000),1,(9121010569135238449/25000000000000000000),(36484042276540953797/100000000000000000000),(540914279576251667/1000000000000000000),false⟩
theorem valid775 : certificate775.Valid := by decide +kernel
theorem bound775 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate775.a certificate775.b certificate775.c x ≤ (certificate775.bound:ℝ) :=
  rat_majority_certificate_sound certificate775 valid775 x hx0 hx1

def certificate776 : RatMajorityCertificate := ⟨0,(1001273994058899993/1000000000000000000),(258625719/217661000),(43908242608646525751/100000000000000000000),(5488530326080815719/12500000000000000000),(71326879292871441/100000000000000000),false⟩
theorem valid776 : certificate776.Valid := by decide +kernel
theorem bound776 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate776.a certificate776.b certificate776.c x ≤ (certificate776.bound:ℝ) :=
  rat_majority_certificate_sound certificate776 valid776 x hx0 hx1

def certificate777 : RatMajorityCertificate := ⟨(199790167612785663/1000000000000000000),(801229294959549007268190075738799641/1000000000000000000000000000000000000),(258625719/217661000),(39567325635065294283/100000000000000000000),(9891831408766323571/25000000000000000000),(71326879292871441/100000000000000000),false⟩
theorem valid777 : certificate777.Valid := by decide +kernel
theorem bound777 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate777.a certificate777.b certificate777.c x ≤ (certificate777.bound:ℝ) :=
  rat_majority_certificate_sound certificate777 valid777 x hx0 hx1

def certificate778 : RatMajorityCertificate := ⟨0,(1001273994058899993/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(270479273915730863/500000000000000000),false⟩
theorem valid778 : certificate778.Valid := by decide +kernel
theorem bound778 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate778.a certificate778.b certificate778.c x ≤ (certificate778.bound:ℝ) :=
  rat_majority_certificate_sound certificate778 valid778 x hx0 hx1

def certificate779 : RatMajorityCertificate := ⟨(130858328602759771/1000000000000000000),(870248952722942723029610375707418397/1000000000000000000000000000000000000),1,(18240937309512902249/50000000000000000000),(36481874619025804499/100000000000000000000),(270479273915730863/500000000000000000),false⟩
theorem valid779 : certificate779.Valid := by decide +kernel
theorem bound779 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate779.a certificate779.b certificate779.c x ≤ (certificate779.bound:ℝ) :=
  rat_majority_certificate_sound certificate779 valid779 x hx0 hx1

def certificate780 : RatMajorityCertificate := ⟨0,(125168554421373349/125000000000000000),(1290514333/1085715000),(43917915866051967783/100000000000000000000),(5489739483256495973/12500000000000000000),(713639270444238719/1000000000000000000),false⟩
theorem valid780 : certificate780.Valid := by decide +kernel
theorem bound780 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate780.a certificate780.b certificate780.c x ≤ (certificate780.bound:ℝ) :=
  rat_majority_certificate_sound certificate780 valid780 x hx0 hx1

def certificate781 : RatMajorityCertificate := ⟨(99617951476971613/500000000000000000),(50115242229895623567371373052258063/62500000000000000000000000000000000),(1290514333/1085715000),(39592088640540832353/100000000000000000000),(19796044320270416177/50000000000000000000),(713639270444238719/1000000000000000000),false⟩
theorem valid781 : certificate781.Valid := by decide +kernel
theorem bound781 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate781.a certificate781.b certificate781.c x ≤ (certificate781.bound:ℝ) :=
  rat_majority_certificate_sound certificate781 valid781 x hx0 hx1

def certificate782 : RatMajorityCertificate := ⟨0,(125168554421373349/125000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(135226243654557353/250000000000000000),false⟩
theorem valid782 : certificate782.Valid := by decide +kernel
theorem bound782 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate782.a certificate782.b certificate782.c x ≤ (certificate782.bound:ℝ) :=
  rat_majority_certificate_sound certificate782 valid782 x hx0 hx1

def certificate783 : RatMajorityCertificate := ⟨(26009807953707229/200000000000000000),(21778100821931597122422681950760079/25000000000000000000000000000000000),1,(9125272356231538647/25000000000000000000),(36501089424926154589/100000000000000000000),(135226243654557353/250000000000000000),false⟩
theorem valid783 : certificate783.Valid := by decide +kernel
theorem bound783 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate783.a certificate783.b certificate783.c x ≤ (certificate783.bound:ℝ) :=
  rat_majority_certificate_sound certificate783 valid783 x hx0 hx1

def certificate784 : RatMajorityCertificate := ⟨0,(62589015759292061/62500000000000000),(2576003929/2166380000),(21964073052658975901/50000000000000000000),(43928146105317951803/100000000000000000000),(357026893300646913/500000000000000000),false⟩
theorem valid784 : certificate784.Valid := by decide +kernel
theorem bound784 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate784.a certificate784.b certificate784.c x ≤ (certificate784.bound:ℝ) :=
  rat_majority_certificate_sound certificate784 valid784 x hx0 hx1

def certificate785 : RatMajorityCertificate := ⟨(12430706007901283/62500000000000000),(3133787830728093907869307546385737/3906250000000000000000000000000000),(2576003929/2166380000),(39611983873911589057/100000000000000000000),(19805991936955794529/50000000000000000000),(357026893300646913/500000000000000000),false⟩
theorem valid785 : certificate785.Valid := by decide +kernel
theorem bound785 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate785.a certificate785.b certificate785.c x ≤ (certificate785.bound:ℝ) :=
  rat_majority_certificate_sound certificate785 valid785 x hx0 hx1

def certificate786 : RatMajorityCertificate := ⟨0,(62589015759292061/62500000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(270475350442071313/500000000000000000),false⟩
theorem valid786 : certificate786.Valid := by decide +kernel
theorem bound786 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate786.a certificate786.b certificate786.c x ≤ (certificate786.bound:ℝ) :=
  rat_majority_certificate_sound certificate786 valid786 x hx0 hx1

def certificate787 : RatMajorityCertificate := ⟨(130151003064527637/1000000000000000000),(54442992577398671401809939510810143/62500000000000000000000000000000000),1,(4562362048790498949/12500000000000000000),(36498896390323991593/100000000000000000000),(270475350442071313/500000000000000000),false⟩
theorem valid787 : certificate787.Valid := by decide +kernel
theorem bound787 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate787.a certificate787.b certificate787.c x ≤ (certificate787.bound:ℝ) :=
  rat_majority_certificate_sound certificate787 valid787 x hx0 hx1

def certificate788 : RatMajorityCertificate := ⟨0,(1001501369252209983/1000000000000000000),(642421383/540365000),(43923238126332571911/100000000000000000000),(5490404765791571489/12500000000000000000),(356989493420606793/500000000000000000),false⟩
theorem valid788 : certificate788.Valid := by decide +kernel
theorem bound788 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate788.a certificate788.b certificate788.c x ≤ (certificate788.bound:ℝ) :=
  rat_majority_certificate_sound certificate788 valid788 x hx0 hx1

def certificate789 : RatMajorityCertificate := ⟨(24959511146109671/125000000000000000),(100190686567831615462511770360954407/125000000000000000000000000000000000),(642421383/540365000),(9896709319982094417/25000000000000000000),(39586837279928377669/100000000000000000000),(356989493420606793/500000000000000000),false⟩
theorem valid789 : certificate789.Valid := by decide +kernel
theorem bound789 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate789.a certificate789.b certificate789.c x ≤ (certificate789.bound:ℝ) :=
  rat_majority_certificate_sound certificate789 valid789 x hx0 hx1

def certificate790 : RatMajorityCertificate := ⟨0,(1001501369252209983/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(540978149932814201/1000000000000000000),false⟩
theorem valid790 : certificate790.Valid := by decide +kernel
theorem bound790 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate790.a certificate790.b certificate790.c x ≤ (certificate790.bound:ℝ) :=
  rat_majority_certificate_sound certificate790 valid790 x hx0 hx1

def certificate791 : RatMajorityCertificate := ⟨(130078430664181873/1000000000000000000),(871227642831853179139035874101761841/1000000000000000000000000000000000000),1,(36500805059672876019/100000000000000000000),(1825040252983643801/5000000000000000000),(540978149932814201/1000000000000000000),false⟩
theorem valid791 : certificate791.Valid := by decide +kernel
theorem bound791 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate791.a certificate791.b certificate791.c x ≤ (certificate791.bound:ℝ) :=
  rat_majority_certificate_sound certificate791 valid791 x hx0 hx1

def certificate792 : RatMajorityCertificate := ⟨0,(40063189004775533/40000000000000000),(20513561/17253200),(1757025378553385677/4000000000000000000),(21962817231917320963/50000000000000000000),(356944322375139801/500000000000000000),false⟩
theorem valid792 : certificate792.Valid := by decide +kernel
theorem bound792 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate792.a certificate792.b certificate792.c x ≤ (certificate792.bound:ℝ) :=
  rat_majority_certificate_sound certificate792 valid792 x hx0 hx1

def certificate793 : RatMajorityCertificate := ⟨(197345773712471269/1000000000000000000),(32156887973239133638208719943338623/40000000000000000000000000000000000),(20513561/17253200),(39650005561204851429/100000000000000000000),(3965000556120485143/10000000000000000000),(356944322375139801/500000000000000000),false⟩
theorem valid793 : certificate793.Valid := by decide +kernel
theorem bound793 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate793.a certificate793.b certificate793.c x ≤ (certificate793.bound:ℝ) :=
  rat_majority_certificate_sound certificate793 valid793 x hx0 hx1

def certificate794 : RatMajorityCertificate := ⟨0,(40063189004775533/40000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(21637180746436427/40000000000000000),false⟩
theorem valid794 : certificate794.Valid := by decide +kernel
theorem bound794 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate794.a certificate794.b certificate794.c x ≤ (certificate794.bound:ℝ) :=
  rat_majority_certificate_sound certificate794 valid794 x hx0 hx1

def certificate795 : RatMajorityCertificate := ⟨(129295514896422577/1000000000000000000),(34883198354010384875642089401591459/40000000000000000000000000000000000),1,(18259689922046076377/50000000000000000000),(7303875968818430551/20000000000000000000),(21637180746436427/40000000000000000),false⟩
theorem valid795 : certificate795.Valid := by decide +kernel
theorem bound795 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate795.a certificate795.b certificate795.c x ≤ (certificate795.bound:ℝ) :=
  rat_majority_certificate_sound certificate795 valid795 x hx0 hx1

def certificate796 : RatMajorityCertificate := ⟨0,(125207403668051057/125000000000000000),(2559464737/2151970000),(8786883111161833001/20000000000000000000),(21967207777904582503/50000000000000000000),(714224263589594869/1000000000000000000),false⟩
theorem valid796 : certificate796.Valid := by decide +kernel
theorem bound796 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate796.a certificate796.b certificate796.c x ≤ (certificate796.bound:ℝ) :=
  rat_majority_certificate_sound certificate796 valid796 x hx0 hx1

def certificate797 : RatMajorityCertificate := ⟨(196754078128991741/1000000000000000000),(100572336384419132237807862080679763/125000000000000000000000000000000000),(2559464737/2151970000),(198373712088162210932667/500000000000000000000000),(79349484835264884373067/200000000000000000000000),(714224263589594869/1000000000000000000),false⟩
theorem valid797 : certificate797.Valid := by decide +kernel
theorem bound797 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate797.a certificate797.b certificate797.c x ≤ (certificate797.bound:ℝ) :=
  rat_majority_certificate_sound certificate797 valid797 x hx0 hx1

def certificate798 : RatMajorityCertificate := ⟨0,(125207403668051057/125000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(540978544489204803/1000000000000000000),false⟩
theorem valid798 : certificate798.Valid := by decide +kernel
theorem bound798 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate798.a certificate798.b certificate798.c x ≤ (certificate798.bound:ℝ) :=
  rat_majority_certificate_sound certificate798 valid798 x hx0 hx1

def certificate799 : RatMajorityCertificate := ⟨(16176554438694179/125000000000000000),(13625501076942596969805175019302797/15625000000000000000000000000000000),1,(18258424125645013881/50000000000000000000),(36516848251290027763/100000000000000000000),(540978544489204803/1000000000000000000),false⟩
theorem valid799 : certificate799.Valid := by decide +kernel
theorem bound799 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate799.a certificate799.b certificate799.c x ≤ (certificate799.bound:ℝ) :=
  rat_majority_certificate_sound certificate799 valid799 x hx0 hx1

end Cycle12.MajorityCertificates.Batch019
