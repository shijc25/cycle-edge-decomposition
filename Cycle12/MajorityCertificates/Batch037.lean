import Cycle12.RationalMajorityCertificate

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MajorityCertificates.Batch037

def certificate1480 : RatMajorityCertificate := ⟨0,(100015264886047943/100000000000000000),(56534509/46726600),(2219758237466280833/5000000000000000000),(44395164749325616661/100000000000000000000),(365800162111979433/500000000000000000),false⟩
theorem valid1480 : certificate1480.Valid := by decide +kernel
theorem bound1480 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1480.a certificate1480.b certificate1480.c x ≤ (certificate1480.bound:ℝ) :=
  rat_majority_certificate_sound certificate1480 valid1480 x hx0 hx1

def certificate1481 : RatMajorityCertificate := ⟨(6040812382444063/31250000000000000),(2521303577131936907058876666287591/3125000000000000000000000000000000),(56534509/46726600),(20118407519789134111/50000000000000000000),(40236815039578268223/100000000000000000000),(365800162111979433/500000000000000000),false⟩
theorem valid1481 : certificate1481.Valid := by decide +kernel
theorem bound1481 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1481.a certificate1481.b certificate1481.c x ≤ (certificate1481.bound:ℝ) :=
  rat_majority_certificate_sound certificate1481 valid1481 x hx0 hx1

def certificate1482 : RatMajorityCertificate := ⟨0,(100015264886047943/100000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(549203598035334569/1000000000000000000),false⟩
theorem valid1482 : certificate1482.Valid := by decide +kernel
theorem bound1482 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1482.a certificate1482.b certificate1482.c x ≤ (certificate1482.bound:ℝ) :=
  rat_majority_certificate_sound certificate1482 valid1482 x hx0 hx1

def certificate1483 : RatMajorityCertificate := ⟨(1275101344633821/6250000000000000),(497565806797692129576924814719797/625000000000000000000000000000000),1,(8658673230889712499/25000000000000000000),(34634692923558849997/100000000000000000000),(549203598035334569/1000000000000000000),false⟩
theorem valid1483 : certificate1483.Valid := by decide +kernel
theorem bound1483 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1483.a certificate1483.b certificate1483.c x ≤ (certificate1483.bound:ℝ) :=
  rat_majority_certificate_sound certificate1483 valid1483 x hx0 hx1

def certificate1484 : RatMajorityCertificate := ⟨0,(500079911332688487/500000000000000000),(2826685369/2334740000),(44413075799678582407/100000000000000000000),(5551634474959822801/12500000000000000000),(732246157711804631/1000000000000000000),false⟩
theorem valid1484 : certificate1484.Valid := by decide +kernel
theorem bound1484 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1484.a certificate1484.b certificate1484.c x ≤ (certificate1484.bound:ℝ) :=
  rat_majority_certificate_sound certificate1484 valid1484 x hx0 hx1

def certificate1485 : RatMajorityCertificate := ⟨(192354123257377021/1000000000000000000),(403887478429662354010166596294942773/500000000000000000000000000000000000),(2826685369/2334740000),(8055960570441728061/20000000000000000000),(20139901426104320153/50000000000000000000),(732246157711804631/1000000000000000000),false⟩
theorem valid1485 : certificate1485.Valid := by decide +kernel
theorem bound1485 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1485.a certificate1485.b certificate1485.c x ≤ (certificate1485.bound:ℝ) :=
  rat_majority_certificate_sound certificate1485 valid1485 x hx0 hx1

def certificate1486 : RatMajorityCertificate := ⟨0,(500079911332688487/500000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(137286915059496267/250000000000000000),false⟩
theorem valid1486 : certificate1486.Valid := by decide +kernel
theorem bound1486 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1486.a certificate1486.b certificate1486.c x ≤ (certificate1486.bound:ℝ) :=
  rat_majority_certificate_sound certificate1486 valid1486 x hx0 hx1

def certificate1487 : RatMajorityCertificate := ⟨(50891730267725907/250000000000000000),(99570045873320651261463886069467291/125000000000000000000000000000000000),1,(6929370335116954341/20000000000000000000),(17323425837792385853/50000000000000000000),(137286915059496267/250000000000000000),false⟩
theorem valid1487 : certificate1487.Valid := by decide +kernel
theorem bound1487 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1487.a certificate1487.b certificate1487.c x ≤ (certificate1487.bound:ℝ) :=
  rat_majority_certificate_sound certificate1487 valid1487 x hx0 hx1

def certificate1488 : RatMajorityCertificate := ⟨0,(1000167072050760799/1000000000000000000),(942227273/777730000),(22215441936808403833/50000000000000000000),(44430883873616807667/100000000000000000000),(183221880895145799/250000000000000000),false⟩
theorem valid1488 : certificate1488.Valid := by decide +kernel
theorem bound1488 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1488.a certificate1488.b certificate1488.c x ≤ (certificate1488.bound:ℝ) :=
  rat_majority_certificate_sound certificate1488 valid1488 x hx0 hx1

def certificate1489 : RatMajorityCertificate := ⟨(191385005756465297/1000000000000000000),(808750091208898902021081838108507697/1000000000000000000000000000000000000),(942227273/777730000),(5040383797828233969/12500000000000000000),(40323070382625871753/100000000000000000000),(183221880895145799/250000000000000000),false⟩
theorem valid1489 : certificate1489.Valid := by decide +kernel
theorem bound1489 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1489.a certificate1489.b certificate1489.c x ≤ (certificate1489.bound:ℝ) :=
  rat_majority_certificate_sound certificate1489 valid1489 x hx0 hx1

def certificate1490 : RatMajorityCertificate := ⟨0,(1000167072050760799/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(274563336913167701/500000000000000000),false⟩
theorem valid1490 : certificate1490.Valid := by decide +kernel
theorem bound1490 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1490.a certificate1490.b certificate1490.c x ≤ (certificate1490.bound:ℝ) :=
  rat_majority_certificate_sound certificate1490 valid1490 x hx0 hx1

def certificate1491 : RatMajorityCertificate := ⟨(25422967069057633/125000000000000000),(99593669470042815156763370371871233/125000000000000000000000000000000000),1,(1732591239274013809/5000000000000000000),(34651824785480276181/100000000000000000000),(274563336913167701/500000000000000000),false⟩
theorem valid1491 : certificate1491.Valid := by decide +kernel
theorem bound1491 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1491.a certificate1491.b certificate1491.c x ≤ (certificate1491.bound:ℝ) :=
  rat_majority_certificate_sound certificate1491 valid1491 x hx0 hx1

def certificate1492 : RatMajorityCertificate := ⟨0,(1000174390977563221/1000000000000000000),(353337617/291458750),(22224285775305668539/50000000000000000000),(44448571550611337079/100000000000000000000),(366761362169672749/500000000000000000),false⟩
theorem valid1492 : certificate1492.Valid := by decide +kernel
theorem bound1492 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1492.a certificate1492.b certificate1492.c x ≤ (certificate1492.bound:ℝ) :=
  rat_majority_certificate_sound certificate1492 valid1492 x hx0 hx1

def certificate1493 : RatMajorityCertificate := ⟨(23798496996597833/125000000000000000),(101219151632441797549950126330899907/125000000000000000000000000000000000),(353337617/291458750),(2018343393740416719/5000000000000000000),(40366867874808334381/100000000000000000000),(366761362169672749/500000000000000000),false⟩
theorem valid1493 : certificate1493.Valid := by decide +kernel
theorem bound1493 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1493.a certificate1493.b certificate1493.c x ≤ (certificate1493.bound:ℝ) :=
  rat_majority_certificate_sound certificate1493 valid1493 x hx0 hx1

def certificate1494 : RatMajorityCertificate := ⟨0,(1000174390977563221/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(274514759268336531/500000000000000000),false⟩
theorem valid1494 : certificate1494.Valid := by decide +kernel
theorem bound1494 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1494.a certificate1494.b certificate1494.c x ≤ (certificate1494.bound:ℝ) :=
  rat_majority_certificate_sound certificate1494 valid1494 x hx0 hx1

def certificate1495 : RatMajorityCertificate := ⟨(202618049193793403/1000000000000000000),(797521007024098959565829697754768937/1000000000000000000000000000000000000),1,(8668122973212073313/25000000000000000000),(34672491892848293253/100000000000000000000),(274514759268336531/500000000000000000),false⟩
theorem valid1495 : certificate1495.Valid := by decide +kernel
theorem bound1495 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1495.a certificate1495.b certificate1495.c x ≤ (certificate1495.bound:ℝ) :=
  rat_majority_certificate_sound certificate1495 valid1495 x hx0 hx1

def certificate1496 : RatMajorityCertificate := ⟨0,(500090885591078837/500000000000000000),(1413390123/1165100000),(2779141513818033351/6250000000000000000),(44466264221088533617/100000000000000000000),(367080596447226497/500000000000000000),false⟩
theorem valid1496 : certificate1496.Valid := by decide +kernel
theorem bound1496 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1496.a certificate1496.b certificate1496.c x ≤ (certificate1496.bound:ℝ) :=
  rat_majority_certificate_sound certificate1496 valid1496 x hx0 hx1

def certificate1497 : RatMajorityCertificate := ⟨(189409358368304249/1000000000000000000),(405368991825435545907076141838921587/500000000000000000000000000000000000),(1413390123/1165100000),(4041014733482511791/10000000000000000000),(40410147334825117911/100000000000000000000),(367080596447226497/500000000000000000),false⟩
theorem valid1497 : certificate1497.Valid := by decide +kernel
theorem bound1497 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1497.a certificate1497.b certificate1497.c x ≤ (certificate1497.bound:ℝ) :=
  rat_majority_certificate_sound certificate1497 valid1497 x hx0 hx1

def certificate1498 : RatMajorityCertificate := ⟨0,(500090885591078837/500000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(54899413499007261/100000000000000000),false⟩
theorem valid1498 : certificate1498.Valid := by decide +kernel
theorem bound1498 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1498.a certificate1498.b certificate1498.c x ≤ (certificate1498.bound:ℝ) :=
  rat_majority_certificate_sound certificate1498 valid1498 x hx0 hx1

def certificate1499 : RatMajorityCertificate := ⟨(101161879561518211/500000000000000000),(199455308857561718297437010887799393/250000000000000000000000000000000000),1,(693608935838192217/2000000000000000000),(34680446791909610851/100000000000000000000),(54899413499007261/100000000000000000),false⟩
theorem valid1499 : certificate1499.Valid := by decide +kernel
theorem bound1499 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1499.a certificate1499.b certificate1499.c x ≤ (certificate1499.bound:ℝ) :=
  rat_majority_certificate_sound certificate1499 valid1499 x hx0 hx1

def certificate1500 : RatMajorityCertificate := ⟨0,(50009460409776771/50000000000000000),(40969319/33750000),(44483957698936393429/100000000000000000000),(4448395769893639343/10000000000000000000),(367400490991315919/500000000000000000),false⟩
theorem valid1500 : certificate1500.Valid := by decide +kernel
theorem bound1500 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1500.a certificate1500.b certificate1500.c x ≤ (certificate1500.bound:ℝ) :=
  rat_majority_certificate_sound certificate1500 valid1500 x hx0 hx1

def certificate1501 : RatMajorityCertificate := ⟨(7537204469358613/40000000000000000),(1623446887880288747700479123821377/2000000000000000000000000000000000),(40969319/33750000),(1264168409214612253/3125000000000000000),(40453389094867592097/100000000000000000000),(367400490991315919/500000000000000000),false⟩
theorem valid1501 : certificate1501.Valid := by decide +kernel
theorem bound1501 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1501.a certificate1501.b certificate1501.c x ≤ (certificate1501.bound:ℝ) :=
  rat_majority_certificate_sound certificate1501 valid1501 x hx0 hx1

def certificate1502 : RatMajorityCertificate := ⟨0,(50009460409776771/50000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(21958463810895989/40000000000000000),false⟩
theorem valid1502 : certificate1502.Valid := by decide +kernel
theorem bound1502 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1502.a certificate1502.b certificate1502.c x ≤ (certificate1502.bound:ℝ) :=
  rat_majority_certificate_sound certificate1502 valid1502 x hx0 hx1

def certificate1503 : RatMajorityCertificate := ⟨(25256353888183481/125000000000000000),(4988125921355672965736618100280149/6250000000000000000000000000000000),1,(17343911330022045013/50000000000000000000),(34687822660044090027/100000000000000000000),(21958463810895989/40000000000000000),false⟩
theorem valid1503 : certificate1503.Valid := by decide +kernel
theorem bound1503 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1503.a certificate1503.b certificate1503.c x ≤ (certificate1503.bound:ℝ) :=
  rat_majority_certificate_sound certificate1503 valid1503 x hx0 hx1

def certificate1504 : RatMajorityCertificate := ⟨0,(250049173214760727/250000000000000000),(565406641/465470000),(22250766556617891059/50000000000000000000),(44501533113235782119/100000000000000000000),(22982373824386657/31250000000000000),false⟩
theorem valid1504 : certificate1504.Valid := by decide +kernel
theorem bound1504 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1504.a certificate1504.b certificate1504.c x ≤ (certificate1504.bound:ℝ) :=
  rat_majority_certificate_sound certificate1504 valid1504 x hx0 hx1

def certificate1505 : RatMajorityCertificate := ⟨(93718328230984769/500000000000000000),(101590396118153052731843050083632937/125000000000000000000000000000000000),(565406641/465470000),(20248406105718140483/50000000000000000000),(40496812211436280967/100000000000000000000),(22982373824386657/31250000000000000),false⟩
theorem valid1505 : certificate1505.Valid := by decide +kernel
theorem bound1505 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1505.a certificate1505.b certificate1505.c x ≤ (certificate1505.bound:ℝ) :=
  rat_majority_certificate_sound certificate1505 valid1505 x hx0 hx1

def certificate1506 : RatMajorityCertificate := ⟨0,(250049173214760727/250000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(548873960960232817/1000000000000000000),false⟩
theorem valid1506 : certificate1506.Valid := by decide +kernel
theorem bound1506 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1506.a certificate1506.b certificate1506.c x ≤ (certificate1506.bound:ℝ) :=
  rat_majority_certificate_sound certificate1506 valid1506 x hx0 hx1

def certificate1507 : RatMajorityCertificate := ⟨(100677464880200341/500000000000000000),(99850269752728158608443213861192093/125000000000000000000000000000000000),1,(34706561634130671693/100000000000000000000),(17353280817065335847/50000000000000000000),(548873960960232817/1000000000000000000),false⟩
theorem valid1507 : certificate1507.Valid := by decide +kernel
theorem bound1507 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1507.a certificate1507.b certificate1507.c x ≤ (certificate1507.bound:ℝ) :=
  rat_majority_certificate_sound certificate1507 valid1507 x hx0 hx1

def certificate1508 : RatMajorityCertificate := ⟨0,(1000204220006616269/1000000000000000000),(148689137/122420000),(8899782999545134437/20000000000000000000),(22249457498862836093/50000000000000000000),(367594952568330507/500000000000000000),false⟩
theorem valid1508 : certificate1508.Valid := by decide +kernel
theorem bound1508 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1508.a certificate1508.b certificate1508.c x ≤ (certificate1508.bound:ℝ) :=
  rat_majority_certificate_sound certificate1508 valid1508 x hx0 hx1

def certificate1509 : RatMajorityCertificate := ⟨(37173999878565311/200000000000000000),(162859252448256789009185024568355341/200000000000000000000000000000000000),(148689137/122420000),(40533600827124836693/100000000000000000000),(20266800413562418347/50000000000000000000),(367594952568330507/500000000000000000),false⟩
theorem valid1509 : certificate1509.Valid := by decide +kernel
theorem bound1509 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1509.a certificate1509.b certificate1509.c x ≤ (certificate1509.bound:ℝ) :=
  rat_majority_certificate_sound certificate1509 valid1509 x hx0 hx1

def certificate1510 : RatMajorityCertificate := ⟨0,(1000204220006616269/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(34301008801446371/62500000000000000),false⟩
theorem valid1510 : certificate1510.Valid := by decide +kernel
theorem bound1510 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1510.a certificate1510.b certificate1510.c x ≤ (certificate1510.bound:ℝ) :=
  rat_majority_certificate_sound certificate1510 valid1510 x hx0 hx1

def certificate1511 : RatMajorityCertificate := ⟨(12555422740047709/62500000000000000),(49954776941850765215111147284422279/62500000000000000000000000000000000),1,(34719164532493702043/100000000000000000000),(8679791133123425511/25000000000000000000),(34301008801446371/62500000000000000),false⟩
theorem valid1511 : certificate1511.Valid := by decide +kernel
theorem bound1511 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1511.a certificate1511.b certificate1511.c x ≤ (certificate1511.bound:ℝ) :=
  rat_majority_certificate_sound certificate1511 valid1511 x hx0 hx1

def certificate1512 : RatMajorityCertificate := ⟨0,(125026472863647463/125000000000000000),(2823457469/2324640000),(44498833264384918577/100000000000000000000),(22249416632192459289/50000000000000000000),(367556006135646799/500000000000000000),false⟩
theorem valid1512 : certificate1512.Valid := by decide +kernel
theorem bound1512 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1512.a certificate1512.b certificate1512.c x ≤ (certificate1512.bound:ℝ) :=
  rat_majority_certificate_sound certificate1512 valid1512 x hx0 hx1

def certificate1513 : RatMajorityCertificate := ⟨(185000672088050089/1000000000000000000),(101896491355074325910904620018225793/125000000000000000000000000000000000),(2823457469/2324640000),(40555401955082667961/100000000000000000000),(20277700977541333981/50000000000000000000),(367556006135646799/500000000000000000),false⟩
theorem valid1513 : certificate1513.Valid := by decide +kernel
theorem bound1513 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1513.a certificate1513.b certificate1513.c x ≤ (certificate1513.bound:ℝ) :=
  rat_majority_certificate_sound certificate1513 valid1513 x hx0 hx1

def certificate1514 : RatMajorityCertificate := ⟨0,(125026472863647463/125000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(68595557175532567/125000000000000000),false⟩
theorem valid1514 : certificate1514.Valid := by decide +kernel
theorem bound1514 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1514.a certificate1514.b certificate1514.c x ≤ (certificate1514.bound:ℝ) :=
  rat_majority_certificate_sound certificate1514 valid1514 x hx0 hx1

def certificate1515 : RatMajorityCertificate := ⟨(50116274469370009/250000000000000000),(24990757185940068161638672518862833/31250000000000000000000000000000000),1,(4341313632602782611/12500000000000000000),(34730509060822260889/100000000000000000000),(68595557175532567/125000000000000000),false⟩
theorem valid1515 : certificate1515.Valid := by decide +kernel
theorem bound1515 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1515.a certificate1515.b certificate1515.c x ≤ (certificate1515.bound:ℝ) :=
  rat_majority_certificate_sound certificate1515 valid1515 x hx0 hx1

def certificate1516 : RatMajorityCertificate := ⟨0,(1000219373892906593/1000000000000000000),(176464483/145208750),(44513608555779401459/100000000000000000000),(2225680427788970073/5000000000000000000),(735568258327585539/1000000000000000000),false⟩
theorem valid1516 : certificate1516.Valid := by decide +kernel
theorem bound1516 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1516.a certificate1516.b certificate1516.c x ≤ (certificate1516.bound:ℝ) :=
  rat_majority_certificate_sound certificate1516 valid1516 x hx0 hx1

def certificate1517 : RatMajorityCertificate := ⟨(91638220227432381/500000000000000000),(408451363685910591964422554543412067/500000000000000000000000000000000000),(176464483/145208750),(40614035251092985709/100000000000000000000),(4061403525109298571/10000000000000000000),(735568258327585539/1000000000000000000),false⟩
theorem valid1517 : certificate1517.Valid := by decide +kernel
theorem bound1517 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1517.a certificate1517.b certificate1517.c x ≤ (certificate1517.bound:ℝ) :=
  rat_majority_certificate_sound certificate1517 valid1517 x hx0 hx1

def certificate1518 : RatMajorityCertificate := ⟨0,(1000219373892906593/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(274338756413075707/500000000000000000),false⟩
theorem valid1518 : certificate1518.Valid := by decide +kernel
theorem bound1518 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1518.a certificate1518.b certificate1518.c x ≤ (certificate1518.bound:ℝ) :=
  rat_majority_certificate_sound certificate1518 valid1518 x hx0 hx1

def certificate1519 : RatMajorityCertificate := ⟨(9988559527518507/50000000000000000),(40020217937938741675869649170183349/50000000000000000000000000000000000),1,(17374568319407625439/50000000000000000000),(34749136638815250879/100000000000000000000),(274338756413075707/500000000000000000),false⟩
theorem valid1519 : certificate1519.Valid := by decide +kernel
theorem bound1519 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1519.a certificate1519.b certificate1519.c x ≤ (certificate1519.bound:ℝ) :=
  rat_majority_certificate_sound certificate1519 valid1519 x hx0 hx1

end Cycle12.MajorityCertificates.Batch037
