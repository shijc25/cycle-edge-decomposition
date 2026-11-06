import Cycle12.RationalMajorityCertificate

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MajorityCertificates.Batch011

def certificate440 : RatMajorityCertificate := ⟨0,(1007509859805086087/1000000000000000000),(1157434067/979330000),(21881997697629607087/50000000000000000000),(1750559815810368567/4000000000000000000),(710296386059502789/1000000000000000000),false⟩
theorem valid440 : certificate440.Valid := by decide +kernel
theorem bound440 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate440.a certificate440.b certificate440.c x ≤ (certificate440.bound:ℝ) :=
  rat_majority_certificate_sound certificate440 valid440 x hx0 hx1

def certificate441 : RatMajorityCertificate := ⟨(192394660077351721/1000000000000000000),(813670342803306261440512446617394273/1000000000000000000000000000000000000),(1157434067/979330000),(19816417771082115363/50000000000000000000),(39632835542164230727/100000000000000000000),(710296386059502789/1000000000000000000),false⟩
theorem valid441 : certificate441.Valid := by decide +kernel
theorem bound441 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate441.a certificate441.b certificate441.c x ≤ (certificate441.bound:ℝ) :=
  rat_majority_certificate_sound certificate441 valid441 x hx0 hx1

def certificate442 : RatMajorityCertificate := ⟨0,(1007509859805086087/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(67904611631354251/125000000000000000),false⟩
theorem valid442 : certificate442.Valid := by decide +kernel
theorem bound442 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate442.a certificate442.b certificate442.c x ≤ (certificate442.bound:ℝ) :=
  rat_majority_certificate_sound certificate442 valid442 x hx0 hx1

def certificate443 : RatMajorityCertificate := ⟨(62679132724576489/500000000000000000),(440605085678500601531112014738791457/500000000000000000000000000000000000),1,(36626381494541351731/100000000000000000000),(9156595373635337933/25000000000000000000),(67904611631354251/125000000000000000),false⟩
theorem valid443 : certificate443.Valid := by decide +kernel
theorem bound443 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate443.a certificate443.b certificate443.c x ≤ (certificate443.bound:ℝ) :=
  rat_majority_certificate_sound certificate443 valid443 x hx0 hx1

def certificate444 : RatMajorityCertificate := ⟨0,(1007554842616099643/1000000000000000000),(144561282/122373125),(5468937218430628167/12500000000000000000),(43751497747445025337/100000000000000000000),(709793239327513341/1000000000000000000),false⟩
theorem valid444 : certificate444.Valid := by decide +kernel
theorem bound444 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate444.a certificate444.b certificate444.c x ≤ (certificate444.bound:ℝ) :=
  rat_majority_certificate_sound certificate444 valid444 x hx0 hx1

def certificate445 : RatMajorityCertificate := ⟨(38408081048415531/200000000000000000),(162812720467297218890705023635244567/200000000000000000000000000000000000),(144561282/122373125),(19814531086624371093/50000000000000000000),(39629062173248742187/100000000000000000000),(709793239327513341/1000000000000000000),false⟩
theorem valid445 : certificate445.Valid := by decide +kernel
theorem bound445 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate445.a certificate445.b certificate445.c x ≤ (certificate445.bound:ℝ) :=
  rat_majority_certificate_sound certificate445 valid445 x hx0 hx1

def certificate446 : RatMajorityCertificate := ⟨0,(1007554842616099643/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(543228879864249283/1000000000000000000),false⟩
theorem valid446 : certificate446.Valid := by decide +kernel
theorem bound446 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate446.a certificate446.b certificate446.c x ≤ (certificate446.bound:ℝ) :=
  rat_majority_certificate_sound certificate446 valid446 x hx0 hx1

def certificate447 : RatMajorityCertificate := ⟨(6254026401355829/50000000000000000),(44076467544269977842938081037130953/50000000000000000000000000000000000),1,(1831646110694447207/5000000000000000000),(36632922213888944141/100000000000000000000),(543228879864249283/1000000000000000000),false⟩
theorem valid447 : certificate447.Valid := by decide +kernel
theorem bound447 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate447.a certificate447.b certificate447.c x ≤ (certificate447.bound:ℝ) :=
  rat_majority_certificate_sound certificate447 valid447 x hx0 hx1

def certificate448 : RatMajorityCertificate := ⟨0,(503799859209192939/500000000000000000),(2310975469/1957290000),(10934369138469286177/25000000000000000000),(43737476553877144709/100000000000000000000),(709191443579303783/1000000000000000000),false⟩
theorem valid448 : certificate448.Valid := by decide +kernel
theorem bound448 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate448.a certificate448.b certificate448.c x ≤ (certificate448.bound:ℝ) :=
  rat_majority_certificate_sound certificate448 valid448 x hx0 hx1

def certificate449 : RatMajorityCertificate := ⟨(47817818691526381/250000000000000000),(101859354477816529478770182962576241/125000000000000000000000000000000000),(2310975469/1957290000),(7926851556499233337/20000000000000000000),(19817128891248083343/50000000000000000000),(709191443579303783/1000000000000000000),false⟩
theorem valid449 : certificate449.Valid := by decide +kernel
theorem bound449 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate449.a certificate449.b certificate449.c x ≤ (certificate449.bound:ℝ) :=
  rat_majority_certificate_sound certificate449 valid449 x hx0 hx1

def certificate450 : RatMajorityCertificate := ⟨0,(503799859209192939/500000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(543243730882188723/1000000000000000000),false⟩
theorem valid450 : certificate450.Valid := by decide +kernel
theorem bound450 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate450.a certificate450.b certificate450.c x ≤ (certificate450.bound:ℝ) :=
  rat_majority_certificate_sound certificate450 valid450 x hx0 hx1

def certificate451 : RatMajorityCertificate := ⟨(25004853652551421/200000000000000000),(88162530092136708085108244392383681/100000000000000000000000000000000000),1,(36634336499501994167/100000000000000000000),(4579292062437749271/12500000000000000000),(543243730882188723/1000000000000000000),false⟩
theorem valid451 : certificate451.Valid := by decide +kernel
theorem bound451 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate451.a certificate451.b certificate451.c x ≤ (certificate451.bound:ℝ) :=
  rat_majority_certificate_sound certificate451 valid451 x hx0 hx1

def certificate452 : RatMajorityCertificate := ⟨0,(1007609054914311749/1000000000000000000),(9241387/7829400),(21864655492887103467/50000000000000000000),(8745862197154841387/20000000000000000000),(708868521549395381/1000000000000000000),false⟩
theorem valid452 : certificate452.Valid := by decide +kernel
theorem bound452 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate452.a certificate452.b certificate452.c x ≤ (certificate452.bound:ℝ) :=
  rat_majority_certificate_sound certificate452 valid452 x hx0 hx1

def certificate453 : RatMajorityCertificate := ⟨(38243572210145959/200000000000000000),(162987241331649943454620866681427709/200000000000000000000000000000000000),(9241387/7829400),(39627177768819445369/100000000000000000000),(3962717776881944537/10000000000000000000),(708868521549395381/1000000000000000000),false⟩
theorem valid453 : certificate453.Valid := by decide +kernel
theorem bound453 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate453.a certificate453.b certificate453.c x ≤ (certificate453.bound:ℝ) :=
  rat_majority_certificate_sound certificate453 valid453 x hx0 hx1

def certificate454 : RatMajorityCertificate := ⟨0,(1007609054914311749/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(543208350460567919/1000000000000000000),false⟩
theorem valid454 : certificate454.Valid := by decide +kernel
theorem bound454 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate454.a certificate454.b certificate454.c x ≤ (certificate454.bound:ℝ) :=
  rat_majority_certificate_sound certificate454 valid454 x hx0 hx1

def certificate455 : RatMajorityCertificate := ⟨(124640054129784273/1000000000000000000),(882020607768131158571534526360676523/1000000000000000000000000000000000000),1,(4580405602891557323/12500000000000000000),(7328648964626491717/20000000000000000000),(543208350460567919/1000000000000000000),false⟩
theorem valid455 : certificate455.Valid := by decide +kernel
theorem bound455 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate455.a certificate455.b certificate455.c x ≤ (certificate455.bound:ℝ) :=
  rat_majority_certificate_sound certificate455 valid455 x hx0 hx1

def certificate456 : RatMajorityCertificate := ⟨0,(25190784851077311/25000000000000000),(461889581/391402000),(10930875229252360653/25000000000000000000),(43723500917009442613/100000000000000000000),(708672269556265717/1000000000000000000),false⟩
theorem valid456 : certificate456.Valid := by decide +kernel
theorem bound456 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate456.a certificate456.b certificate456.c x ≤ (certificate456.bound:ℝ) :=
  rat_majority_certificate_sound certificate456 valid456 x hx0 hx1

def certificate457 : RatMajorityCertificate := ⟨(47861414161443919/250000000000000000),(5092029625960089193178493540178191/6250000000000000000000000000000000),(461889581/391402000),(39615440670438585223/100000000000000000000),(4951930083804823153/12500000000000000000),(708672269556265717/1000000000000000000),false⟩
theorem valid457 : certificate457.Valid := by decide +kernel
theorem bound457 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate457.a certificate457.b certificate457.c x ≤ (certificate457.bound:ℝ) :=
  rat_majority_certificate_sound certificate457 valid457 x hx0 hx1

def certificate458 : RatMajorityCertificate := ⟨0,(25190784851077311/25000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(135800792132831507/250000000000000000),false⟩
theorem valid458 : certificate458.Valid := by decide +kernel
theorem bound458 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate458.a certificate458.b certificate458.c x ≤ (certificate458.bound:ℝ) :=
  rat_majority_certificate_sound certificate458 valid458 x hx0 hx1

def certificate459 : RatMajorityCertificate := ⟨(4979603951508661/40000000000000000),(882191262257063345724810402909429/1000000000000000000000000000000000),1,(36646766696710276297/100000000000000000000),(18323383348355138149/50000000000000000000),(135800792132831507/250000000000000000),false⟩
theorem valid459 : certificate459.Valid := by decide +kernel
theorem bound459 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate459.a certificate459.b certificate459.c x ≤ (certificate459.bound:ℝ) :=
  rat_majority_certificate_sound certificate459 valid459 x hx0 hx1

def certificate460 : RatMajorityCertificate := ⟨0,(503844588202218837/500000000000000000),(2307403363/1955950000),(1366069526554789003/3125000000000000000),(43714224849753248097/100000000000000000000),(88529799454754543/125000000000000000),false⟩
theorem valid460 : certificate460.Valid := by decide +kernel
theorem bound460 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate460.a certificate460.b certificate460.c x ≤ (certificate460.bound:ℝ) :=
  rat_majority_certificate_sound certificate460 valid460 x hx0 hx1

def certificate461 : RatMajorityCertificate := ⟨(190379358720382763/1000000000000000000),(407922978605545084064721745471293369/500000000000000000000000000000000000),(2307403363/1955950000),(39633140969785926257/100000000000000000000),(19816570484892963129/50000000000000000000),(88529799454754543/125000000000000000),false⟩
theorem valid461 : certificate461.Valid := by decide +kernel
theorem bound461 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate461.a certificate461.b certificate461.c x ≤ (certificate461.bound:ℝ) :=
  rat_majority_certificate_sound certificate461 valid461 x hx0 hx1

def certificate462 : RatMajorityCertificate := ⟨0,(503844588202218837/500000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(271626267412090611/500000000000000000),false⟩
theorem valid462 : certificate462.Valid := by decide +kernel
theorem bound462 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate462.a certificate462.b certificate462.c x ≤ (certificate462.bound:ℝ) :=
  rat_majority_certificate_sound certificate462 valid462 x hx0 hx1

def certificate463 : RatMajorityCertificate := ⟨(124710502820443909/1000000000000000000),(441009876264160624850750120898286167/500000000000000000000000000000000000),1,(18320908414489354819/50000000000000000000),(36641816828978709639/100000000000000000000),(271626267412090611/500000000000000000),false⟩
theorem valid463 : certificate463.Valid := by decide +kernel
theorem bound463 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate463.a certificate463.b certificate463.c x ≤ (certificate463.bound:ℝ) :=
  rat_majority_certificate_sound certificate463 valid463 x hx0 hx1

def certificate464 : RatMajorityCertificate := ⟨0,(503866876508971011/500000000000000000),(1152978537/977645000),(21853207714570301851/50000000000000000000),(43706415429140603703/100000000000000000000),(708026018612808923/1000000000000000000),false⟩
theorem valid464 : certificate464.Valid := by decide +kernel
theorem bound464 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate464.a certificate464.b certificate464.c x ≤ (certificate464.bound:ℝ) :=
  rat_majority_certificate_sound certificate464 valid464 x hx0 hx1

def certificate465 : RatMajorityCertificate := ⟨(191150129198640063/1000000000000000000),(407552657965365984496734359309786307/500000000000000000000000000000000000),(1152978537/977645000),(2475351625812342347/6250000000000000000),(39605626012997477553/100000000000000000000),(708026018612808923/1000000000000000000),false⟩
theorem valid465 : certificate465.Valid := by decide +kernel
theorem bound465 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate465.a certificate465.b certificate465.c x ≤ (certificate465.bound:ℝ) :=
  rat_majority_certificate_sound certificate465 valid465 x hx0 hx1

def certificate466 : RatMajorityCertificate := ⟨0,(503866876508971011/500000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(271621997769384597/500000000000000000),false⟩
theorem valid466 : certificate466.Valid := by decide +kernel
theorem bound466 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate466.a certificate466.b certificate466.c x ≤ (certificate466.bound:ℝ) :=
  rat_majority_certificate_sound certificate466 valid466 x hx0 hx1

def certificate467 : RatMajorityCertificate := ⟨(124428591950368567/1000000000000000000),(441171430534529507854827756631388763/500000000000000000000000000000000000),1,(36648443761845856141/100000000000000000000),(18324221880922928071/50000000000000000000),(271621997769384597/500000000000000000),false⟩
theorem valid467 : certificate467.Valid := by decide +kernel
theorem bound467 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate467.a certificate467.b certificate467.c x ≤ (certificate467.bound:ℝ) :=
  rat_majority_certificate_sound certificate467 valid467 x hx0 hx1

def certificate468 : RatMajorityCertificate := ⟨0,(251944552748274553/250000000000000000),(2303845921/1954640000),(8738135229665412079/20000000000000000000),(10922669037081765099/25000000000000000000),(707325227637123699/1000000000000000000),false⟩
theorem valid468 : certificate468.Valid := by decide +kernel
theorem bound468 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate468.a certificate468.b certificate468.c x ≤ (certificate468.bound:ℝ) :=
  rat_majority_certificate_sound certificate468 valid468 x hx0 hx1

def certificate469 : RatMajorityCertificate := ⟨(95017470968455991/500000000000000000),(102033142147717470099677084234302977/125000000000000000000000000000000000),(2303845921/1954640000),(39617796682172033817/100000000000000000000),(19808898341086016909/50000000000000000000),(707325227637123699/1000000000000000000),false⟩
theorem valid469 : certificate469.Valid := by decide +kernel
theorem bound469 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate469.a certificate469.b certificate469.c x ≤ (certificate469.bound:ℝ) :=
  rat_majority_certificate_sound certificate469 valid469 x hx0 hx1

def certificate470 : RatMajorityCertificate := ⟨0,(251944552748274553/250000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(543240676075739313/1000000000000000000),false⟩
theorem valid470 : certificate470.Valid := by decide +kernel
theorem bound470 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate470.a certificate470.b certificate470.c x ≤ (certificate470.bound:ℝ) :=
  rat_majority_certificate_sound certificate470 valid470 x hx0 hx1

def certificate471 : RatMajorityCertificate := ⟨(15524693377747153/125000000000000000),(27581707163923712895443732941902391/31250000000000000000000000000000000),1,(36653891869015553287/100000000000000000000),(4581736483626944161/12500000000000000000),(543240676075739313/1000000000000000000),false⟩
theorem valid471 : certificate471.Valid := by decide +kernel
theorem bound471 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate471.a certificate471.b certificate471.c x ≤ (certificate471.bound:ℝ) :=
  rat_majority_certificate_sound certificate471 valid471 x hx0 hx1

def certificate472 : RatMajorityCertificate := ⟨0,(1007822547311514569/1000000000000000000),(2300755627/1954000000),(21831649207427859143/50000000000000000000),(43663298414855718287/100000000000000000000),(22059388010058807/31250000000000000),false⟩
theorem valid472 : certificate472.Valid := by decide +kernel
theorem bound472 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate472.a certificate472.b certificate472.c x ≤ (certificate472.bound:ℝ) :=
  rat_majority_certificate_sound certificate472 valid472 x hx0 hx1

def certificate473 : RatMajorityCertificate := ⟨(93019958414391437/500000000000000000),(410163662215754152753812889105654347/500000000000000000000000000000000000),(2300755627/1954000000),(39690569496683491733/100000000000000000000),(19845284748341745867/50000000000000000000),(22059388010058807/31250000000000000),false⟩
theorem valid473 : certificate473.Valid := by decide +kernel
theorem bound473 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate473.a certificate473.b certificate473.c x ≤ (certificate473.bound:ℝ) :=
  rat_majority_certificate_sound certificate473 valid473 x hx0 hx1

def certificate474 : RatMajorityCertificate := ⟨0,(1007822547311514569/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(543231012909283037/1000000000000000000),false⟩
theorem valid474 : certificate474.Valid := by decide +kernel
theorem bound474 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate474.a certificate474.b certificate474.c x ≤ (certificate474.bound:ℝ) :=
  rat_majority_certificate_sound certificate474 valid474 x hx0 hx1

def certificate475 : RatMajorityCertificate := ⟨(3872036341443953/31250000000000000),(27592129074568028178984459143548743/31250000000000000000000000000000000),1,(18330376456184839101/50000000000000000000),(36660752912369678203/100000000000000000000),(543231012909283037/1000000000000000000),false⟩
theorem valid475 : certificate475.Valid := by decide +kernel
theorem bound475 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate475.a certificate475.b certificate475.c x ≤ (certificate475.bound:ℝ) :=
  rat_majority_certificate_sound certificate475 valid475 x hx0 hx1

def certificate476 : RatMajorityCertificate := ⟨0,(1007975690753832627/1000000000000000000),(143974483/121430625),(43850293639728532479/100000000000000000000),(8564510476509479/19531250000000000),(44678421616491321/62500000000000000),false⟩
theorem valid476 : certificate476.Valid := by decide +kernel
theorem bound476 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate476.a certificate476.b certificate476.c x ≤ (certificate476.bound:ℝ) :=
  rat_majority_certificate_sound certificate476 valid476 x hx0 hx1

def certificate477 : RatMajorityCertificate := ⟨(100845534731125517/500000000000000000),(402337997846870451657734182853156841/500000000000000000000000000000000000),(143974483/121430625),(39485462988964814481/100000000000000000000),(19742731494482407241/50000000000000000000),(44678421616491321/62500000000000000),false⟩
theorem valid477 : certificate477.Valid := by decide +kernel
theorem bound477 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate477.a certificate477.b certificate477.c x ≤ (certificate477.bound:ℝ) :=
  rat_majority_certificate_sound certificate477 valid477 x hx0 hx1

def certificate478 : RatMajorityCertificate := ⟨0,(1007975690753832627/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(67936047914669581/125000000000000000),false⟩
theorem valid478 : certificate478.Valid := by decide +kernel
theorem bound478 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate478.a certificate478.b certificate478.c x ≤ (certificate478.bound:ℝ) :=
  rat_majority_certificate_sound certificate478 valid478 x hx0 hx1

def certificate479 : RatMajorityCertificate := ⟨(125717084258078919/1000000000000000000),(881255925909237750661472912516909787/1000000000000000000000000000000000000),1,(18309624619663527433/50000000000000000000),(36619249239327054867/100000000000000000000),(67936047914669581/125000000000000000),false⟩
theorem valid479 : certificate479.Valid := by decide +kernel
theorem bound479 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate479.a certificate479.b certificate479.c x ≤ (certificate479.bound:ℝ) :=
  rat_majority_certificate_sound certificate479 valid479 x hx0 hx1

end Cycle12.MajorityCertificates.Batch011
