import Cycle12.RationalMajorityCertificate

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MajorityCertificates.Batch039

def certificate1560 : RatMajorityCertificate := ⟨0,(1000289891537334381/1000000000000000000),(1393586781/1156640000),(44282912700575139701/100000000000000000000),(22141456350287569851/50000000000000000000),(72432055364461153/100000000000000000),false⟩
theorem valid1560 : certificate1560.Valid := by decide +kernel
theorem bound1560 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1560.a certificate1560.b certificate1560.c x ≤ (certificate1560.bound:ℝ) :=
  rat_majority_certificate_sound certificate1560 valid1560 x hx0 hx1

def certificate1561 : RatMajorityCertificate := ⟨(162308482554846989/1000000000000000000),(837934357126957156846853795615971191/1000000000000000000000000000000000000),(1393586781/1156640000),(10222510969261954627/25000000000000000000),(40890043877047818509/100000000000000000000),(72432055364461153/100000000000000000),false⟩
theorem valid1561 : certificate1561.Valid := by decide +kernel
theorem bound1561 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1561.a certificate1561.b certificate1561.c x ≤ (certificate1561.bound:ℝ) :=
  rat_majority_certificate_sound certificate1561 valid1561 x hx0 hx1

def certificate1562 : RatMajorityCertificate := ⟨0,(1000289891537334381/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(547616940719799529/1000000000000000000),false⟩
theorem valid1562 : certificate1562.Valid := by decide +kernel
theorem bound1562 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1562.a certificate1562.b certificate1562.c x ≤ (certificate1562.bound:ℝ) :=
  rat_majority_certificate_sound certificate1562 valid1562 x hx0 hx1

def certificate1563 : RatMajorityCertificate := ⟨(19127513142806679/100000000000000000),(80895931106736407294358619536869301/100000000000000000000000000000000000),1,(34975076709343120847/100000000000000000000),(2185942294333945053/6250000000000000000),(547616940719799529/1000000000000000000),false⟩
theorem valid1563 : certificate1563.Valid := by decide +kernel
theorem bound1563 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1563.a certificate1563.b certificate1563.c x ≤ (certificate1563.bound:ℝ) :=
  rat_majority_certificate_sound certificate1563 valid1563 x hx0 hx1

def certificate1564 : RatMajorityCertificate := ⟨0,(1000293607850076141/1000000000000000000),(1392215693/1156405000),(44261906877285488671/100000000000000000000),(1383184589915171521/3125000000000000000),(361681552317927791/500000000000000000),false⟩
theorem valid1564 : certificate1564.Valid := by decide +kernel
theorem bound1564 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1564.a certificate1564.b certificate1564.c x ≤ (certificate1564.bound:ℝ) :=
  rat_majority_certificate_sound certificate1564 valid1564 x hx0 hx1

def certificate1565 : RatMajorityCertificate := ⟨(503425675156583/3125000000000000),(2622344039644749086542691352613797/3125000000000000000000000000000000),(1392215693/1156405000),(40897518595263798493/100000000000000000000),(20448759297631899247/50000000000000000000),(361681552317927791/500000000000000000),false⟩
theorem valid1565 : certificate1565.Valid := by decide +kernel
theorem bound1565 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1565.a certificate1565.b certificate1565.c x ≤ (certificate1565.bound:ℝ) :=
  rat_majority_certificate_sound certificate1565 valid1565 x hx0 hx1

def certificate1566 : RatMajorityCertificate := ⟨0,(1000293607850076141/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(547556091256836551/1000000000000000000),false⟩
theorem valid1566 : certificate1566.Valid := by decide +kernel
theorem bound1566 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1566.a certificate1566.b certificate1566.c x ≤ (certificate1566.bound:ℝ) :=
  rat_majority_certificate_sound certificate1566 valid1566 x hx0 hx1

def certificate1567 : RatMajorityCertificate := ⟨(95391469287800709/500000000000000000),(404727326953024166100738991916216031/500000000000000000000000000000000000),1,(34988050159033959547/100000000000000000000),(8747012539758489887/25000000000000000000),(547556091256836551/1000000000000000000),false⟩
theorem valid1567 : certificate1567.Valid := by decide +kernel
theorem bound1567 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1567.a certificate1567.b certificate1567.c x ≤ (certificate1567.bound:ℝ) :=
  rat_majority_certificate_sound certificate1567 valid1567 x hx0 hx1

def certificate1568 : RatMajorityCertificate := ⟨0,(250075706785576827/250000000000000000),(555769689/462268000),(4422502528827433771/10000000000000000000),(44225025288274337711/100000000000000000000),(721760171526555343/1000000000000000000),false⟩
theorem valid1568 : certificate1568.Valid := by decide +kernel
theorem bound1568 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1568.a certificate1568.b certificate1568.c x ≤ (certificate1568.bound:ℝ) :=
  rat_majority_certificate_sound certificate1568 valid1568 x hx0 hx1

def certificate1569 : RatMajorityCertificate := ⟨(159837097418851773/1000000000000000000),(210104331678002372330481796183335729/250000000000000000000000000000000000),(555769689/462268000),(10222419356443356329/25000000000000000000),(40889677425773425317/100000000000000000000),(721760171526555343/1000000000000000000),false⟩
theorem valid1569 : certificate1569.Valid := by decide +kernel
theorem bound1569 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1569.a certificate1569.b certificate1569.c x ≤ (certificate1569.bound:ℝ) :=
  rat_majority_certificate_sound certificate1569 valid1569 x hx0 hx1

def certificate1570 : RatMajorityCertificate := ⟨0,(250075706785576827/250000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(17109683290821257/31250000000000000),false⟩
theorem valid1570 : certificate1570.Valid := by decide +kernel
theorem bound1570 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1570.a certificate1570.b certificate1570.c x ≤ (certificate1570.bound:ℝ) :=
  rat_majority_certificate_sound certificate1570 valid1570 x hx0 hx1

def certificate1571 : RatMajorityCertificate := ⟨(95193602151424949/500000000000000000),(101232246053305812543994221035943177/125000000000000000000000000000000000),1,(1093703043180727159/3125000000000000000),(34998497381783269089/100000000000000000000),(17109683290821257/31250000000000000),false⟩
theorem valid1571 : certificate1571.Valid := by decide +kernel
theorem bound1571 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1571.a certificate1571.b certificate1571.c x ≤ (certificate1571.bound:ℝ) :=
  rat_majority_certificate_sound certificate1571 valid1571 x hx0 hx1

def certificate1572 : RatMajorityCertificate := ⟨0,(15629847426498737/15625000000000000),(692862157/577615000),(44163532631145750279/100000000000000000000),(1104088315778643757/2500000000000000000),(719023152695157489/1000000000000000000),false⟩
theorem valid1572 : certificate1572.Valid := by decide +kernel
theorem bound1572 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1572.a certificate1572.b certificate1572.c x ≤ (certificate1572.bound:ℝ) :=
  rat_majority_certificate_sound certificate1572 valid1572 x hx0 hx1

def certificate1573 : RatMajorityCertificate := ⟨(156960302584814787/1000000000000000000),(13176581845081006544291068965575981/15625000000000000000000000000000000),(692862157/577615000),(20447526439402446273/50000000000000000000),(40895052878804892547/100000000000000000000),(719023152695157489/1000000000000000000),false⟩
theorem valid1573 : certificate1573.Valid := by decide +kernel
theorem bound1573 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1573.a certificate1573.b certificate1573.c x ≤ (certificate1573.bound:ℝ) :=
  rat_majority_certificate_sound certificate1573 valid1573 x hx0 hx1

def certificate1574 : RatMajorityCertificate := ⟨0,(15629847426498737/15625000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(547358889319958347/1000000000000000000),false⟩
theorem valid1574 : certificate1574.Valid := by decide +kernel
theorem bound1574 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1574.a certificate1574.b certificate1574.c x ≤ (certificate1574.bound:ℝ) :=
  rat_majority_certificate_sound certificate1574 valid1574 x hx0 hx1

def certificate1575 : RatMajorityCertificate := ⟨(94584012074778623/500000000000000000),(6336590035534464373353486735900849/7812500000000000000000000000000000),1,(35030547860467926063/100000000000000000000),(2189409241279245379/6250000000000000000),(547358889319958347/1000000000000000000),false⟩
theorem valid1575 : certificate1575.Valid := by decide +kernel
theorem bound1575 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1575.a certificate1575.b certificate1575.c x ≤ (certificate1575.bound:ℝ) :=
  rat_majority_certificate_sound certificate1575 valid1575 x hx0 hx1

def certificate1576 : RatMajorityCertificate := ⟨0,(20006240001444841/20000000000000000),(2766988429/2310590000),(44118672796833561799/100000000000000000000),(220593363984167809/500000000000000000),(179245771373603359/250000000000000000),false⟩
theorem valid1576 : certificate1576.Valid := by decide +kernel
theorem bound1576 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1576.a certificate1576.b certificate1576.c x ≤ (certificate1576.bound:ℝ) :=
  rat_majority_certificate_sound certificate1576 valid1576 x hx0 hx1

def certificate1577 : RatMajorityCertificate := ⟨(154312184600461709/1000000000000000000),(16919033401180743367825524303906731/20000000000000000000000000000000000),(2766988429/2310590000),(1636474079727199253/4000000000000000000),(20455925996589990663/50000000000000000000),(179245771373603359/250000000000000000),false⟩
theorem valid1577 : certificate1577.Valid := by decide +kernel
theorem bound1577 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1577.a certificate1577.b certificate1577.c x ≤ (certificate1577.bound:ℝ) :=
  rat_majority_certificate_sound certificate1577 valid1577 x hx0 hx1

def certificate1578 : RatMajorityCertificate := ⟨0,(20006240001444841/20000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(273594970261446157/500000000000000000),false⟩
theorem valid1578 : certificate1578.Valid := by decide +kernel
theorem bound1578 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1578.a certificate1578.b certificate1578.c x ≤ (certificate1578.bound:ℝ) :=
  rat_majority_certificate_sound certificate1578 valid1578 x hx0 hx1

def certificate1579 : RatMajorityCertificate := ⟨(37564226540887831/200000000000000000),(3249729068643322105294997085370129/4000000000000000000000000000000000),1,(35065842376303110649/100000000000000000000),(701316847526062213/2000000000000000000),(273594970261446157/500000000000000000),false⟩
theorem valid1579 : certificate1579.Valid := by decide +kernel
theorem bound1579 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1579.a certificate1579.b certificate1579.c x ≤ (certificate1579.bound:ℝ) :=
  rat_majority_certificate_sound certificate1579 valid1579 x hx0 hx1

def certificate1580 : RatMajorityCertificate := ⟨0,(1000315633883359749/1000000000000000000),(172647529/144386250),(22039194367421244667/50000000000000000000),(8815677746968497867/20000000000000000000),(7152184657567021/10000000000000000),false⟩
theorem valid1580 : certificate1580.Valid := by decide +kernel
theorem bound1580 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1580.a certificate1580.b certificate1580.c x ≤ (certificate1580.bound:ℝ) :=
  rat_majority_certificate_sound certificate1580 valid1580 x hx0 hx1

def certificate1581 : RatMajorityCertificate := ⟨(38167874169849531/250000000000000000),(211898987226646590386440011928072281/250000000000000000000000000000000000),(172647529/144386250),(20454630511060866131/50000000000000000000),(40909261022121732263/100000000000000000000),(7152184657567021/10000000000000000),false⟩
theorem valid1581 : certificate1581.Valid := by decide +kernel
theorem bound1581 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1581.a certificate1581.b certificate1581.c x ≤ (certificate1581.bound:ℝ) :=
  rat_majority_certificate_sound certificate1581 valid1581 x hx0 hx1

def certificate1582 : RatMajorityCertificate := ⟨0,(1000315633883359749/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(10942058602990651/20000000000000000),false⟩
theorem valid1582 : certificate1582.Valid := by decide +kernel
theorem bound1582 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1582.a certificate1582.b certificate1582.c x ≤ (certificate1582.bound:ℝ) :=
  rat_majority_certificate_sound certificate1582 valid1582 x hx0 hx1

def certificate1583 : RatMajorityCertificate := ⟨(18711640885950249/100000000000000000),(81314016474508860368666233416872499/100000000000000000000000000000000000),1,(17542141816860651621/50000000000000000000),(35084283633721303243/100000000000000000000),(10942058602990651/20000000000000000),false⟩
theorem valid1583 : certificate1583.Valid := by decide +kernel
theorem bound1583 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1583.a certificate1583.b certificate1583.c x ≤ (certificate1583.bound:ℝ) :=
  rat_majority_certificate_sound certificate1583 valid1583 x hx0 hx1

def certificate1584 : RatMajorityCertificate := ⟨0,(1000319252477980607/1000000000000000000),(2759746911/2309770000),(220288411274740947/500000000000000000),(44057682254948189401/100000000000000000000),(357144143772767507/500000000000000000),false⟩
theorem valid1584 : certificate1584.Valid := by decide +kernel
theorem bound1584 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1584.a certificate1584.b certificate1584.c x ≤ (certificate1584.bound:ℝ) :=
  rat_majority_certificate_sound certificate1584 valid1584 x hx0 hx1

def certificate1585 : RatMajorityCertificate := ⟨(151524911876004203/1000000000000000000),(848745965898384196552069846315508779/1000000000000000000000000000000000000),(2759746911/2309770000),(40915077783476056617/100000000000000000000),(20457538891738028309/50000000000000000000),(357144143772767507/500000000000000000),false⟩
theorem valid1585 : certificate1585.Valid := by decide +kernel
theorem bound1585 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1585.a certificate1585.b certificate1585.c x ≤ (certificate1585.bound:ℝ) :=
  rat_majority_certificate_sound certificate1585 valid1585 x hx0 hx1

def certificate1586 : RatMajorityCertificate := ⟨0,(1000319252477980607/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(546995522680627001/1000000000000000000),false⟩
theorem valid1586 : certificate1586.Valid := by decide +kernel
theorem bound1586 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1586.a certificate1586.b certificate1586.c x ≤ (certificate1586.bound:ℝ) :=
  rat_majority_certificate_sound certificate1586 valid1586 x hx0 hx1

def certificate1587 : RatMajorityCertificate := ⟨(186247641781453117/1000000000000000000),(814012150675370716658473993794297981/1000000000000000000000000000000000000),1,(8776744937161384643/25000000000000000000),(35106979748645538573/100000000000000000000),(546995522680627001/1000000000000000000),false⟩
theorem valid1587 : certificate1587.Valid := by decide +kernel
theorem bound1587 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1587.a certificate1587.b certificate1587.c x ≤ (certificate1587.bound:ℝ) :=
  rat_majority_certificate_sound certificate1587 valid1587 x hx0 hx1

def certificate1588 : RatMajorityCertificate := ⟨0,(50016142755018703/50000000000000000),(2755197411/2309360000),(8803606908349227677/20000000000000000000),(22009017270873069193/50000000000000000000),(142513769619841583/200000000000000000),false⟩
theorem valid1588 : certificate1588.Valid := by decide +kernel
theorem bound1588 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1588.a certificate1588.b certificate1588.c x ≤ (certificate1588.bound:ℝ) :=
  rat_majority_certificate_sound certificate1588 valid1588 x hx0 hx1

def certificate1589 : RatMajorityCertificate := ⟨(150054811537466601/1000000000000000000),(42510979880083345978199189007161497/50000000000000000000000000000000000),(2755197411/2309360000),(5113621002432783739/12500000000000000000),(40908968019462269913/100000000000000000000),(142513769619841583/200000000000000000),false⟩
theorem valid1589 : certificate1589.Valid := by decide +kernel
theorem bound1589 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1589.a certificate1589.b certificate1589.c x ≤ (certificate1589.bound:ℝ) :=
  rat_majority_certificate_sound certificate1589 valid1589 x hx0 hx1

def certificate1590 : RatMajorityCertificate := ⟨0,(50016142755018703/50000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(273455622563319901/500000000000000000),false⟩
theorem valid1590 : certificate1590.Valid := by decide +kernel
theorem bound1590 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1590.a certificate1590.b certificate1590.c x ≤ (certificate1590.bound:ℝ) :=
  rat_majority_certificate_sound certificate1590 valid1590 x hx0 hx1

def certificate1591 : RatMajorityCertificate := ⟨(185561983509087269/1000000000000000000),(40735048097923767748165343445807893/50000000000000000000000000000000000),1,(35124868416427656553/100000000000000000000),(17562434208213828277/50000000000000000000),(273455622563319901/500000000000000000),false⟩
theorem valid1591 : certificate1591.Valid := by decide +kernel
theorem bound1591 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1591.a certificate1591.b certificate1591.c x ≤ (certificate1591.bound:ℝ) :=
  rat_majority_certificate_sound certificate1591 valid1591 x hx0 hx1

def certificate1592 : RatMajorityCertificate := ⟨0,(500163219084923781/500000000000000000),(687660353/577242500),(43978008513024669391/100000000000000000000),(2748625532064041837/6250000000000000000),(5553332548850539/7812500000000000),false⟩
theorem valid1592 : certificate1592.Valid := by decide +kernel
theorem bound1592 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1592.a certificate1592.b certificate1592.c x ≤ (certificate1592.bound:ℝ) :=
  rat_majority_certificate_sound certificate1592 valid1592 x hx0 hx1

def certificate1593 : RatMajorityCertificate := ⟨(148454751829947767/1000000000000000000),(425911612521203626422602193593852973/500000000000000000000000000000000000),(687660353/577242500),(40905463113234139827/100000000000000000000),(10226365778308534957/25000000000000000000),(5553332548850539/7812500000000000),false⟩
theorem valid1593 : certificate1593.Valid := by decide +kernel
theorem bound1593 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1593.a certificate1593.b certificate1593.c x ≤ (certificate1593.bound:ℝ) :=
  rat_majority_certificate_sound certificate1593 valid1593 x hx0 hx1

def certificate1594 : RatMajorityCertificate := ⟨0,(500163219084923781/500000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(546827505659451001/1000000000000000000),false⟩
theorem valid1594 : certificate1594.Valid := by decide +kernel
theorem bound1594 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1594.a certificate1594.b certificate1594.c x ≤ (certificate1594.bound:ℝ) :=
  rat_majority_certificate_sound certificate1594 valid1594 x hx0 hx1

def certificate1595 : RatMajorityCertificate := ⟨(36975895099249127/200000000000000000),(81538661095597855539052580874210813/100000000000000000000000000000000000),1,(8785662867250579529/25000000000000000000),(35142651469002318117/100000000000000000000),(546827505659451001/1000000000000000000),false⟩
theorem valid1595 : certificate1595.Valid := by decide +kernel
theorem bound1595 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1595.a certificate1595.b certificate1595.c x ≤ (certificate1595.bound:ℝ) :=
  rat_majority_certificate_sound certificate1595 valid1595 x hx0 hx1

def certificate1596 : RatMajorityCertificate := ⟨0,(200066000454631823/200000000000000000),(2746161679/2308590000),(43938532109796093771/100000000000000000000),(10984633027449023443/25000000000000000000),(177280878945322679/250000000000000000),false⟩
theorem valid1596 : certificate1596.Valid := by decide +kernel
theorem bound1596 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1596.a certificate1596.b certificate1596.c x ≤ (certificate1596.bound:ℝ) :=
  rat_majority_certificate_sound certificate1596 valid1596 x hx0 hx1

def certificate1597 : RatMajorityCertificate := ⟨(2940400502920477/20000000000000000),(3413045840738548667525146717460429/4000000000000000000000000000000000),(2746161679/2308590000),(20449280883128899177/50000000000000000000),(8179712353251559671/20000000000000000000),(177280878945322679/250000000000000000),false⟩
theorem valid1597 : certificate1597.Valid := by decide +kernel
theorem bound1597 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1597.a certificate1597.b certificate1597.c x ≤ (certificate1597.bound:ℝ) :=
  rat_majority_certificate_sound certificate1597 valid1597 x hx0 hx1

def certificate1598 : RatMajorityCertificate := ⟨0,(200066000454631823/200000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(546743936747947763/1000000000000000000),false⟩
theorem valid1598 : certificate1598.Valid := by decide +kernel
theorem bound1598 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1598.a certificate1598.b certificate1598.c x ≤ (certificate1598.bound:ℝ) :=
  rat_majority_certificate_sound certificate1598 valid1598 x hx0 hx1

def certificate1599 : RatMajorityCertificate := ⟨(1151232409964423/6250000000000000),(1020090038986119752593191006366871/1250000000000000000000000000000000),1,(2197525341856208933/6250000000000000000),(35160405469699342929/100000000000000000000),(546743936747947763/1000000000000000000),false⟩
theorem valid1599 : certificate1599.Valid := by decide +kernel
theorem bound1599 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1599.a certificate1599.b certificate1599.c x ≤ (certificate1599.bound:ℝ) :=
  rat_majority_certificate_sound certificate1599 valid1599 x hx0 hx1

end Cycle12.MajorityCertificates.Batch039
