import Cycle12.RationalMajorityCertificate

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MajorityCertificates.Batch036

def certificate1440 : RatMajorityCertificate := ⟨0,(1000086551637646667/1000000000000000000),(281296267/235434000),(44057326880340365851/100000000000000000000),(11014331720085091463/25000000000000000000),(359221047454486463/500000000000000000),false⟩
theorem valid1440 : certificate1440.Valid := by decide +kernel
theorem bound1440 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1440.a certificate1440.b certificate1440.c x ≤ (certificate1440.bound:ℝ) :=
  rat_majority_certificate_sound certificate1440 valid1440 x hx0 hx1

def certificate1441 : RatMajorityCertificate := ⟨(198739750308098759/1000000000000000000),(801329600078693252359938394216813747/1000000000000000000000000000000000000),(281296267/235434000),(39744864047463320549/100000000000000000000),(794897280949266411/2000000000000000000),(359221047454486463/500000000000000000),false⟩
theorem valid1441 : certificate1441.Valid := by decide +kernel
theorem bound1441 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1441.a certificate1441.b certificate1441.c x ≤ (certificate1441.bound:ℝ) :=
  rat_majority_certificate_sound certificate1441 valid1441 x hx0 hx1

def certificate1442 : RatMajorityCertificate := ⟨0,(1000086551637646667/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(549516977321384721/1000000000000000000),false⟩
theorem valid1442 : certificate1442.Valid := by decide +kernel
theorem bound1442 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1442.a certificate1442.b certificate1442.c x ≤ (certificate1442.bound:ℝ) :=
  rat_majority_certificate_sound certificate1442 valid1442 x hx0 hx1

def certificate1443 : RatMajorityCertificate := ⟨(206604399903116501/1000000000000000000),(793464269785373544377964589224647833/1000000000000000000000000000000000000),1,(1728216505093521891/5000000000000000000),(34564330101870437821/100000000000000000000),(549516977321384721/1000000000000000000),false⟩
theorem valid1443 : certificate1443.Valid := by decide +kernel
theorem bound1443 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1443.a certificate1443.b certificate1443.c x ≤ (certificate1443.bound:ℝ) :=
  rat_majority_certificate_sound certificate1443 valid1443 x hx0 hx1

def certificate1444 : RatMajorityCertificate := ⟨0,(1000092600208837503/1000000000000000000),(234521553/196030000),(44092378776929453773/100000000000000000000),(22046189388464726887/50000000000000000000),(359868833976674227/500000000000000000),false⟩
theorem valid1444 : certificate1444.Valid := by decide +kernel
theorem bound1444 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1444.a certificate1444.b certificate1444.c x ≤ (certificate1444.bound:ℝ) :=
  rat_majority_certificate_sound certificate1444 valid1444 x hx0 hx1

def certificate1445 : RatMajorityCertificate := ⟨(197610599279146897/1000000000000000000),(802463702146928852877547162060321809/1000000000000000000000000000000000000),(234521553/196030000),(39810610393160456041/100000000000000000000),(19905305196580228021/50000000000000000000),(359868833976674227/500000000000000000),false⟩
theorem valid1445 : certificate1445.Valid := by decide +kernel
theorem bound1445 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1445.a certificate1445.b certificate1445.c x ≤ (certificate1445.bound:ℝ) :=
  rat_majority_certificate_sound certificate1445 valid1445 x hx0 hx1

def certificate1446 : RatMajorityCertificate := ⟨0,(1000092600208837503/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(274746695825131817/500000000000000000),false⟩
theorem valid1446 : certificate1446.Valid := by decide +kernel
theorem bound1446 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1446.a certificate1446.b certificate1446.c x ≤ (certificate1446.bound:ℝ) :=
  rat_majority_certificate_sound certificate1446 valid1446 x hx0 hx1

def certificate1447 : RatMajorityCertificate := ⟨(206406891362980831/1000000000000000000),(793666595524610960180812216617095007/1000000000000000000000000000000000000),1,(17284858457247929171/50000000000000000000),(34569716914495858343/100000000000000000000),(274746695825131817/500000000000000000),false⟩
theorem valid1447 : certificate1447.Valid := by decide +kernel
theorem bound1447 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1447.a certificate1447.b certificate1447.c x ≤ (certificate1447.bound:ℝ) :=
  rat_majority_certificate_sound certificate1447 valid1447 x hx0 hx1

def certificate1448 : RatMajorityCertificate := ⟨0,(500049395558434681/500000000000000000),(1407962177/1175210000),(5516314152719901097/12500000000000000000),(44130513221759208777/100000000000000000000),(360619564912762473/500000000000000000),false⟩
theorem valid1448 : certificate1448.Valid := by decide +kernel
theorem bound1448 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1448.a certificate1448.b certificate1448.c x ≤ (certificate1448.bound:ℝ) :=
  rat_majority_certificate_sound certificate1448 valid1448 x hx0 hx1

def certificate1449 : RatMajorityCertificate := ⟨(197285233228397459/1000000000000000000),(401397033929969718523601959842124421/500000000000000000000000000000000000),(1407962177/1175210000),(9964687105192104421/25000000000000000000),(7971749684153683537/20000000000000000000),(360619564912762473/500000000000000000),false⟩
theorem valid1449 : certificate1449.Valid := by decide +kernel
theorem bound1449 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1449.a certificate1449.b certificate1449.c x ≤ (certificate1449.bound:ℝ) :=
  rat_majority_certificate_sound certificate1449 valid1449 x hx0 hx1

def certificate1450 : RatMajorityCertificate := ⟨0,(500049395558434681/500000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(274735564181589867/500000000000000000),false⟩
theorem valid1450 : certificate1450.Valid := by decide +kernel
theorem bound1450 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1450.a certificate1450.b certificate1450.c x ≤ (certificate1450.bound:ℝ) :=
  rat_majority_certificate_sound certificate1450 valid1450 x hx0 hx1

def certificate1451 : RatMajorityCertificate := ⟨(206218842398254509/1000000000000000000),(396929788064427411247669413309773371/500000000000000000000000000000000000),1,(2160927853726510507/6250000000000000000),(34574845659624168113/100000000000000000000),(274735564181589867/500000000000000000),false⟩
theorem valid1451 : certificate1451.Valid := by decide +kernel
theorem bound1451 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1451.a certificate1451.b certificate1451.c x ≤ (certificate1451.bound:ℝ) :=
  rat_majority_certificate_sound certificate1451 valid1451 x hx0 hx1

def certificate1452 : RatMajorityCertificate := ⟨0,(50005255889401657/50000000000000000),(939212797/782840000),(8833730257877882237/20000000000000000000),(22084325644694705593/50000000000000000000),(722743840430748537/1000000000000000000),false⟩
theorem valid1452 : certificate1452.Valid := by decide +kernel
theorem bound1452 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1452.a certificate1452.b certificate1452.c x ≤ (certificate1452.bound:ℝ) :=
  rat_majority_certificate_sound certificate1452 valid1452 x hx0 hx1

def certificate1453 : RatMajorityCertificate := ⟨(24619360979524737/125000000000000000),(5019559540560522423036620839710791/6250000000000000000000000000000000),(939212797/782840000),(39907014852607055741/100000000000000000000),(19953507426303527871/50000000000000000000),(722743840430748537/1000000000000000000),false⟩
theorem valid1453 : certificate1453.Valid := by decide +kernel
theorem bound1453 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1453.a certificate1453.b certificate1453.c x ≤ (certificate1453.bound:ℝ) :=
  rat_majority_certificate_sound certificate1453 valid1453 x hx0 hx1

def certificate1454 : RatMajorityCertificate := ⟨0,(50005255889401657/50000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(274724132485973399/500000000000000000),false⟩
theorem valid1454 : certificate1454.Valid := by decide +kernel
theorem bound1454 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1454.a certificate1454.b certificate1454.c x ≤ (certificate1454.bound:ℝ) :=
  rat_majority_certificate_sound certificate1454 valid1454 x hx0 hx1

def certificate1455 : RatMajorityCertificate := ⟨(51506429108029753/250000000000000000),(9925721804854060508813290676499279/12500000000000000000000000000000000),1,(6916022142583476933/20000000000000000000),(17290055356458692333/50000000000000000000),(274724132485973399/500000000000000000),false⟩
theorem valid1455 : certificate1455.Valid := by decide +kernel
theorem bound1455 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1455.a certificate1455.b certificate1455.c x ≤ (certificate1455.bound:ℝ) :=
  rat_majority_certificate_sound certificate1455 valid1455 x hx0 hx1

def certificate1456 : RatMajorityCertificate := ⟨0,(1000111573621220377/1000000000000000000),(31326677/26074000),(5525849086418152209/12500000000000000000),(44206792691345217673/100000000000000000000),(724251846865722307/1000000000000000000),false⟩
theorem valid1456 : certificate1456.Valid := by decide +kernel
theorem bound1456 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1456.a certificate1456.b certificate1456.c x ≤ (certificate1456.bound:ℝ) :=
  rat_majority_certificate_sound certificate1456 valid1456 x hx0 hx1

def certificate1457 : RatMajorityCertificate := ⟨(98310004774576379/500000000000000000),(401734813232798917460731694822325117/500000000000000000000000000000000000),(31326677/26074000),(19977698726388664681/50000000000000000000),(39955397452777329363/100000000000000000000),(724251846865722307/1000000000000000000),false⟩
theorem valid1457 : certificate1457.Valid := by decide +kernel
theorem bound1457 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1457.a certificate1457.b certificate1457.c x ≤ (certificate1457.bound:ℝ) :=
  rat_majority_certificate_sound certificate1457 valid1457 x hx0 hx1

def certificate1458 : RatMajorityCertificate := ⟨0,(1000111573621220377/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(274713382188100971/500000000000000000),false⟩
theorem valid1458 : certificate1458.Valid := by decide +kernel
theorem bound1458 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1458.a certificate1458.b certificate1458.c x ≤ (certificate1458.bound:ℝ) :=
  rat_majority_certificate_sound certificate1458 valid1458 x hx0 hx1

def certificate1459 : RatMajorityCertificate := ⟨(20584241178382861/100000000000000000),(79424619525410830923955721839241403/100000000000000000000000000000000000),1,(4323138515014766233/12500000000000000000),(6917021624023625973/20000000000000000000),(274713382188100971/500000000000000000),false⟩
theorem valid1459 : certificate1459.Valid := by decide +kernel
theorem bound1459 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1459.a certificate1459.b certificate1459.c x ≤ (certificate1459.bound:ℝ) :=
  rat_majority_certificate_sound certificate1459 valid1459 x hx0 hx1

def certificate1460 : RatMajorityCertificate := ⟨0,(500059075994526523/500000000000000000),(176325627/146552500),(8848983380632052209/20000000000000000000),(22122458451580130523/50000000000000000000),(72576186643951849/100000000000000000),false⟩
theorem valid1460 : certificate1460.Valid := by decide +kernel
theorem bound1460 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1460.a certificate1460.b certificate1460.c x ≤ (certificate1460.bound:ℝ) :=
  rat_majority_certificate_sound certificate1460 valid1460 x hx0 hx1

def certificate1461 : RatMajorityCertificate := ⟨(19627573585896547/100000000000000000),(40190961288074649448177640274383919/50000000000000000000000000000000000),(176325627/146552500),(40003999634040893937/100000000000000000000),(20001999817020446969/50000000000000000000),(72576186643951849/100000000000000000),false⟩
theorem valid1461 : certificate1461.Valid := by decide +kernel
theorem bound1461 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1461.a certificate1461.b certificate1461.c x ≤ (certificate1461.bound:ℝ) :=
  rat_majority_certificate_sound certificate1461 valid1461 x hx0 hx1

def certificate1462 : RatMajorityCertificate := ⟨0,(500059075994526523/500000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(549403975609073233/1000000000000000000),false⟩
theorem valid1462 : certificate1462.Valid := by decide +kernel
theorem bound1462 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1462.a certificate1462.b certificate1462.c x ≤ (certificate1462.bound:ℝ) :=
  rat_majority_certificate_sound certificate1462 valid1462 x hx0 hx1

def certificate1463 : RatMajorityCertificate := ⟨(102824425106067147/500000000000000000),(198611250989054929103080109089560119/250000000000000000000000000000000000),1,(345903821004906924783187/1000000000000000000000000),(86475955251226731195797/250000000000000000000000),(549403975609073233/1000000000000000000),false⟩
theorem valid1463 : certificate1463.Valid := by decide +kernel
theorem bound1463 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1463.a certificate1463.b certificate1463.c x ≤ (certificate1463.bound:ℝ) :=
  rat_majority_certificate_sound certificate1463 valid1463 x hx0 hx1

def certificate1464 : RatMajorityCertificate := ⟨0,(1000124846239075883/1000000000000000000),(470161483/390510000),(4426304154918259937/10000000000000000000),(44263041549182599371/100000000000000000000),(363205061244378747/500000000000000000),false⟩
theorem valid1464 : certificate1464.Valid := by decide +kernel
theorem bound1464 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1464.a certificate1464.b certificate1464.c x ≤ (certificate1464.bound:ℝ) :=
  rat_majority_certificate_sound certificate1464 valid1464 x hx0 hx1

def certificate1465 : RatMajorityCertificate := ⟨(195352131926076299/1000000000000000000),(804748325334033157642215864091202983/1000000000000000000000000000000000000),(470161483/390510000),(8009331781583429793/20000000000000000000),(20023329453958574483/50000000000000000000),(363205061244378747/500000000000000000),false⟩
theorem valid1465 : certificate1465.Valid := by decide +kernel
theorem bound1465 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1465.a certificate1465.b certificate1465.c x ≤ (certificate1465.bound:ℝ) :=
  rat_majority_certificate_sound certificate1465 valid1465 x hx0 hx1

def certificate1466 : RatMajorityCertificate := ⟨0,(1000124846239075883/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(3433501196091067/6250000000000000),false⟩
theorem valid1466 : certificate1466.Valid := by decide +kernel
theorem bound1466 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1466.a certificate1466.b certificate1466.c x ≤ (certificate1466.bound:ℝ) :=
  rat_majority_certificate_sound certificate1466 valid1466 x hx0 hx1

def certificate1467 : RatMajorityCertificate := ⟨(205295394941337057/1000000000000000000),(794803820939780802012347887897103669/1000000000000000000000000000000000000),1,(1081249497629556161/3125000000000000000),(34599983924145797153/100000000000000000000),(3433501196091067/6250000000000000),false⟩
theorem valid1467 : certificate1467.Valid := by decide +kernel
theorem bound1467 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1467.a certificate1467.b certificate1467.c x ≤ (certificate1467.bound:ℝ) :=
  rat_majority_certificate_sound certificate1467 valid1467 x hx0 hx1

def certificate1468 : RatMajorityCertificate := ⟨0,(100013164969501747/100000000000000000),(235238409/195110000),(44301046223685383117/100000000000000000000),(22150523111842691559/50000000000000000000),(727917967635511527/1000000000000000000),false⟩
theorem valid1468 : certificate1468.Valid := by decide +kernel
theorem bound1468 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1468.a certificate1468.b certificate1468.c x ≤ (certificate1468.bound:ℝ) :=
  rat_majority_certificate_sound certificate1468 valid1468 x hx0 hx1

def certificate1469 : RatMajorityCertificate := ⟨(97488082238626599/500000000000000000),(40256490833258758277422605388831547/50000000000000000000000000000000000),(235238409/195110000),(40095922845184063371/100000000000000000000),(10023980711296015843/25000000000000000000),(727917967635511527/1000000000000000000),false⟩
theorem valid1469 : certificate1469.Valid := by decide +kernel
theorem bound1469 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1469.a certificate1469.b certificate1469.c x ≤ (certificate1469.bound:ℝ) :=
  rat_majority_certificate_sound certificate1469 valid1469 x hx0 hx1

def certificate1470 : RatMajorityCertificate := ⟨0,(100013164969501747/100000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(109868535228122557/200000000000000000),false⟩
theorem valid1470 : certificate1470.Valid := by decide +kernel
theorem bound1470 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1470.a certificate1470.b certificate1470.c x ≤ (certificate1470.bound:ℝ) :=
  rat_majority_certificate_sound certificate1470 valid1470 x hx0 hx1

def certificate1471 : RatMajorityCertificate := ⟨(205140891924505377/1000000000000000000),(79496375103465462009271016887606381/100000000000000000000000000000000000),1,(8651049019639820869/25000000000000000000),(34604196078559283477/100000000000000000000),(109868535228122557/200000000000000000),false⟩
theorem valid1471 : certificate1471.Valid := by decide +kernel
theorem bound1471 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1471.a certificate1471.b certificate1471.c x ≤ (certificate1471.bound:ℝ) :=
  rat_majority_certificate_sound certificate1471 valid1471 x hx0 hx1

def certificate1472 : RatMajorityCertificate := ⟨0,(1000138555658126397/1000000000000000000),(1412496907/1169810000),(44340877433914975989/100000000000000000000),(4434087743391497599/10000000000000000000),(729549192487147443/1000000000000000000),false⟩
theorem valid1472 : certificate1472.Valid := by decide +kernel
theorem bound1472 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1472.a certificate1472.b certificate1472.c x ≤ (certificate1472.bound:ℝ) :=
  rat_majority_certificate_sound certificate1472 valid1472 x hx0 hx1

def certificate1473 : RatMajorityCertificate := ⟨(195078718178474657/1000000000000000000),(805032808219468067517721436032779171/1000000000000000000000000000000000000),(1412496907/1169810000),(40134808429495148329/100000000000000000000),(4013480842949514833/10000000000000000000),(729549192487147443/1000000000000000000),false⟩
theorem valid1473 : certificate1473.Valid := by decide +kernel
theorem bound1473 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1473.a certificate1473.b certificate1473.c x ≤ (certificate1473.bound:ℝ) :=
  rat_majority_certificate_sound certificate1473 valid1473 x hx0 hx1

def certificate1474 : RatMajorityCertificate := ⟨0,(1000138555658126397/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(274662209581518029/500000000000000000),false⟩
theorem valid1474 : certificate1474.Valid := by decide +kernel
theorem bound1474 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1474.a certificate1474.b certificate1474.c x ≤ (certificate1474.bound:ℝ) :=
  rat_majority_certificate_sound certificate1474 valid1474 x hx0 hx1

def certificate1475 : RatMajorityCertificate := ⟨(102490178089110963/500000000000000000),(397564899145875607096846591987609689/500000000000000000000000000000000000),1,(17304285292280188489/50000000000000000000),(34608570584560376979/100000000000000000000),(274662209581518029/500000000000000000),false⟩
theorem valid1475 : certificate1475.Valid := by decide +kernel
theorem bound1475 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1475.a certificate1475.b certificate1475.c x ≤ (certificate1475.bound:ℝ) :=
  rat_majority_certificate_sound certificate1475 valid1475 x hx0 hx1

def certificate1476 : RatMajorityCertificate := ⟨0,(500072778704294447/500000000000000000),(23539133/19483000),(22178560387277672761/50000000000000000000),(44357120774555345523/100000000000000000000),(91260134781050699/125000000000000000),false⟩
theorem valid1476 : certificate1476.Valid := by decide +kernel
theorem bound1476 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1476.a certificate1476.b certificate1476.c x ≤ (certificate1476.bound:ℝ) :=
  rat_majority_certificate_sound certificate1476 valid1476 x hx0 hx1

def certificate1477 : RatMajorityCertificate := ⟨(193677440857946207/1000000000000000000),(403219962682124637785524524585187471/500000000000000000000000000000000000),(23539133/19483000),(10046915844222777233/25000000000000000000),(40187663376891108933/100000000000000000000),(91260134781050699/125000000000000000),false⟩
theorem valid1477 : certificate1477.Valid := by decide +kernel
theorem bound1477 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1477.a certificate1477.b certificate1477.c x ≤ (certificate1477.bound:ℝ) :=
  rat_majority_certificate_sound certificate1477 valid1477 x hx0 hx1

def certificate1478 : RatMajorityCertificate := ⟨0,(500072778704294447/500000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(549223101652636269/1000000000000000000),false⟩
theorem valid1478 : certificate1478.Valid := by decide +kernel
theorem bound1478 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1478.a certificate1478.b certificate1478.c x ≤ (certificate1478.bound:ℝ) :=
  rat_majority_certificate_sound certificate1478 valid1478 x hx0 hx1

def certificate1479 : RatMajorityCertificate := ⟨(25523409268967917/125000000000000000),(49745535142897075011294140635743101/62500000000000000000000000000000000),1,(34630041758814202139/100000000000000000000),(1731502087940710107/5000000000000000000),(549223101652636269/1000000000000000000),false⟩
theorem valid1479 : certificate1479.Valid := by decide +kernel
theorem bound1479 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1479.a certificate1479.b certificate1479.c x ≤ (certificate1479.bound:ℝ) :=
  rat_majority_certificate_sound certificate1479 valid1479 x hx0 hx1

end Cycle12.MajorityCertificates.Batch036
