import Cycle12.RationalMajorityCertificate

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MajorityCertificates.Batch038

def certificate1520 : RatMajorityCertificate := ⟨0,(500113493065233043/500000000000000000),(2821610799/2322080000),(44510851775602423671/100000000000000000000),(5563856471950302959/12500000000000000000),(45957414987672143/62500000000000000),false⟩
theorem valid1520 : certificate1520.Valid := by decide +kernel
theorem bound1520 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1520.a certificate1520.b certificate1520.c x ≤ (certificate1520.bound:ℝ) :=
  rat_majority_certificate_sound certificate1520 valid1520 x hx0 hx1

def certificate1521 : RatMajorityCertificate := ⟨(90855163724185037/500000000000000000),(204618853239500695265603956341422409/250000000000000000000000000000000000),(2821610799/2322080000),(20325171954958056159/50000000000000000000),(40650343909916112319/100000000000000000000),(45957414987672143/62500000000000000),false⟩
theorem valid1521 : certificate1521.Valid := by decide +kernel
theorem bound1521 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1521.a certificate1521.b certificate1521.c x ≤ (certificate1521.bound:ℝ) :=
  rat_majority_certificate_sound certificate1521 valid1521 x hx0 hx1

def certificate1522 : RatMajorityCertificate := ⟨0,(500113493065233043/500000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(548631109017869891/1000000000000000000),false⟩
theorem valid1522 : certificate1522.Valid := by decide +kernel
theorem bound1522 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1522.a certificate1522.b certificate1522.c x ≤ (certificate1522.bound:ℝ) :=
  rat_majority_certificate_sound certificate1522 valid1522 x hx0 hx1

def certificate1523 : RatMajorityCertificate := ⟨(39877763433468363/200000000000000000),(80079291046705724618278771637281391/100000000000000000000000000000000000),1,(17379702524277571669/50000000000000000000),(34759405048555143339/100000000000000000000),(548631109017869891/1000000000000000000),false⟩
theorem valid1523 : certificate1523.Valid := by decide +kernel
theorem bound1523 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1523.a certificate1523.b certificate1523.c x ≤ (certificate1523.bound:ℝ) :=
  rat_majority_certificate_sound certificate1523 valid1523 x hx0 hx1

def certificate1524 : RatMajorityCertificate := ⟨0,(500117306904859123/500000000000000000),(2817707443/2320850000),(11121976611204504177/25000000000000000000),(44487906444818016709/100000000000000000000),(734188057070236127/1000000000000000000),false⟩
theorem valid1524 : certificate1524.Valid := by decide +kernel
theorem bound1524 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1524.a certificate1524.b certificate1524.c x ≤ (certificate1524.bound:ℝ) :=
  rat_majority_certificate_sound certificate1524 valid1524 x hx0 hx1

def certificate1525 : RatMajorityCertificate := ⟨(89784909673668727/500000000000000000),(205155666225738323990360437494253579/250000000000000000000000000000000000),(2817707443/2320850000),(40679847391908289163/100000000000000000000),(10169961847977072291/25000000000000000000),(734188057070236127/1000000000000000000),false⟩
theorem valid1525 : certificate1525.Valid := by decide +kernel
theorem bound1525 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1525.a certificate1525.b certificate1525.c x ≤ (certificate1525.bound:ℝ) :=
  rat_majority_certificate_sound certificate1525 valid1525 x hx0 hx1

def certificate1526 : RatMajorityCertificate := ⟨0,(500117306904859123/500000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(137125767358237751/250000000000000000),false⟩
theorem valid1526 : certificate1526.Valid := by decide +kernel
theorem bound1526 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1526.a certificate1526.b certificate1526.c x ≤ (certificate1526.bound:ℝ) :=
  rat_majority_certificate_sound certificate1526 valid1526 x hx0 hx1

def certificate1527 : RatMajorityCertificate := ⟨(198375023575224939/1000000000000000000),(400906524357229688305923303168731503/500000000000000000000000000000000000),1,(34786539025875698461/100000000000000000000),(17393269512937849231/50000000000000000000),(137125767358237751/250000000000000000),false⟩
theorem valid1527 : certificate1527.Valid := by decide +kernel
theorem bound1527 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1527.a certificate1527.b certificate1527.c x ≤ (certificate1527.bound:ℝ) :=
  rat_majority_certificate_sound certificate1527 valid1527 x hx0 hx1

def certificate1528 : RatMajorityCertificate := ⟨0,(250060562292602329/250000000000000000),(40232299/33138000),(2780493108226475511/6250000000000000000),(44487889731623608177/100000000000000000000),(367061265163526433/500000000000000000),false⟩
theorem valid1528 : certificate1528.Valid := by decide +kernel
theorem bound1528 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1528.a certificate1528.b certificate1528.c x ≤ (certificate1528.bound:ℝ) :=
  rat_majority_certificate_sound certificate1528 valid1528 x hx0 hx1

def certificate1529 : RatMajorityCertificate := ⟨(178790511989142889/1000000000000000000),(205352106332015000067230749964811519/250000000000000000000000000000000000),(40232299/33138000),(635925258260930857/1562500000000000000),(40699216528699574849/100000000000000000000),(367061265163526433/500000000000000000),false⟩
theorem valid1529 : certificate1529.Valid := by decide +kernel
theorem bound1529 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1529.a certificate1529.b certificate1529.c x ≤ (certificate1529.bound:ℝ) :=
  rat_majority_certificate_sound certificate1529 valid1529 x hx0 hx1

def certificate1530 : RatMajorityCertificate := ⟨0,(250060562292602329/250000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(109680357882865819/200000000000000000),false⟩
theorem valid1530 : certificate1530.Valid := by decide +kernel
theorem bound1530 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1530.a certificate1530.b certificate1530.c x ≤ (certificate1530.bound:ℝ) :=
  rat_majority_certificate_sound certificate1530 valid1530 x hx0 hx1

def certificate1531 : RatMajorityCertificate := ⟨(49391492242883687/250000000000000000),(50164276250424381315094705507692977/62500000000000000000000000000000000),1,(6961632234092652903/20000000000000000000),(8702040292615816129/25000000000000000000),(109680357882865819/200000000000000000),false⟩
theorem valid1531 : certificate1531.Valid := by decide +kernel
theorem bound1531 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1531.a certificate1531.b certificate1531.c x ≤ (certificate1531.bound:ℝ) :=
  rat_majority_certificate_sound certificate1531 valid1531 x hx0 hx1

def certificate1532 : RatMajorityCertificate := ⟨0,(500124943242445549/500000000000000000),(351521181/289812500),(44462277476735090211/100000000000000000000),(11115569369183772553/25000000000000000000),(22900638659017973/31250000000000000),false⟩
theorem valid1532 : certificate1532.Valid := by decide +kernel
theorem bound1532 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1532.a certificate1532.b certificate1532.c x ≤ (certificate1532.bound:ℝ) :=
  rat_majority_certificate_sound certificate1532 valid1532 x hx0 hx1

def certificate1533 : RatMajorityCertificate := ⟨(3518456483643727/20000000000000000),(8242831015665577468007826087078877/10000000000000000000000000000000000),(351521181/289812500),(20371823082966478417/50000000000000000000),(8148729233186591367/20000000000000000000),(22900638659017973/31250000000000000),false⟩
theorem valid1533 : certificate1533.Valid := by decide +kernel
theorem bound1533 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1533.a certificate1533.b certificate1533.c x ≤ (certificate1533.bound:ℝ) :=
  rat_majority_certificate_sound certificate1533 valid1533 x hx0 hx1

def certificate1534 : RatMajorityCertificate := ⟨0,(500124943242445549/500000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(109667086049922687/200000000000000000),false⟩
theorem valid1534 : certificate1534.Valid := by decide +kernel
theorem bound1534 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1534.a certificate1534.b certificate1534.c x ≤ (certificate1534.bound:ℝ) :=
  rat_majority_certificate_sound certificate1534 valid1534 x hx0 hx1

def certificate1535 : RatMajorityCertificate := ⟨(98513170478746881/500000000000000000),(200793577826906128227996836603917331/250000000000000000000000000000000000),1,(17411287265852825581/50000000000000000000),(34822574531705651163/100000000000000000000),(109667086049922687/200000000000000000),false⟩
theorem valid1535 : certificate1535.Valid := by decide +kernel
theorem bound1535 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1535.a certificate1535.b certificate1535.c x ≤ (certificate1535.bound:ℝ) :=
  rat_majority_certificate_sound certificate1535 valid1535 x hx0 hx1

def certificate1536 : RatMajorityCertificate := ⟨0,(1000257519061512781/1000000000000000000),(2808406063/2317370000),(44439401565672809011/100000000000000000000),(11109850391418202253/25000000000000000000),(73170055558265463/100000000000000000),false⟩
theorem valid1536 : certificate1536.Valid := by decide +kernel
theorem bound1536 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1536.a certificate1536.b certificate1536.c x ≤ (certificate1536.bound:ℝ) :=
  rat_majority_certificate_sound certificate1536 valid1536 x hx0 hx1

def certificate1537 : RatMajorityCertificate := ⟨(43454970977680189/250000000000000000),(206598218304353768912297511646004391/250000000000000000000000000000000000),(2808406063/2317370000),(20385880912810169483/50000000000000000000),(40771761825620338967/100000000000000000000),(73170055558265463/100000000000000000),false⟩
theorem valid1537 : certificate1537.Valid := by decide +kernel
theorem bound1537 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1537.a certificate1537.b certificate1537.c x ≤ (certificate1537.bound:ℝ) :=
  rat_majority_certificate_sound certificate1537 valid1537 x hx0 hx1

def certificate1538 : RatMajorityCertificate := ⟨0,(1000257519061512781/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(68526980894587001/125000000000000000),false⟩
theorem valid1538 : certificate1538.Valid := by decide +kernel
theorem bound1538 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1538.a certificate1538.b certificate1538.c x ≤ (certificate1538.bound:ℝ) :=
  rat_majority_certificate_sound certificate1538 valid1538 x hx0 hx1

def certificate1539 : RatMajorityCertificate := ⟨(24508995588266963/125000000000000000),(100516882760879623226804171135445897/125000000000000000000000000000000000),1,(6969600755916938669/20000000000000000000),(17424001889792346673/50000000000000000000),(68526980894587001/125000000000000000),false⟩
theorem valid1539 : certificate1539.Valid := by decide +kernel
theorem bound1539 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1539.a certificate1539.b certificate1539.c x ≤ (certificate1539.bound:ℝ) :=
  rat_majority_certificate_sound certificate1539 valid1539 x hx0 hx1

def certificate1540 : RatMajorityCertificate := ⟨0,(1000265139080624063/1000000000000000000),(701178153/579070000),(22208343183364148141/50000000000000000000),(44416686366728296283/100000000000000000000),(73059390099748883/100000000000000000),false⟩
theorem valid1540 : certificate1540.Valid := by decide +kernel
theorem bound1540 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1540.a certificate1540.b certificate1540.c x ≤ (certificate1540.bound:ℝ) :=
  rat_majority_certificate_sound certificate1540 valid1540 x hx0 hx1

def certificate1541 : RatMajorityCertificate := ⟨(171772326994974683/1000000000000000000),(828447268528793276494224623474402971/1000000000000000000000000000000000000),(701178153/579070000),(10199625320288110567/25000000000000000000),(40798501281152442269/100000000000000000000),(73059390099748883/100000000000000000),false⟩
theorem valid1541 : certificate1541.Valid := by decide +kernel
theorem bound1541 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1541.a certificate1541.b certificate1541.c x ≤ (certificate1541.bound:ℝ) :=
  rat_majority_certificate_sound certificate1541 valid1541 x hx0 hx1

def certificate1542 : RatMajorityCertificate := ⟨0,(1000265139080624063/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(27404852302362667/50000000000000000),false⟩
theorem valid1542 : certificate1542.Valid := by decide +kernel
theorem bound1542 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1542.a certificate1542.b certificate1542.c x ≤ (certificate1542.bound:ℝ) :=
  rat_majority_certificate_sound certificate1542 valid1542 x hx0 hx1

def certificate1543 : RatMajorityCertificate := ⟨(195121315009498331/1000000000000000000),(805092089785053955428048351963061147/1000000000000000000000000000000000000),1,(34873286762582320919/100000000000000000000),(871832169064558023/2500000000000000000),(27404852302362667/50000000000000000),false⟩
theorem valid1543 : certificate1543.Valid := by decide +kernel
theorem bound1543 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1543.a certificate1543.b certificate1543.c x ≤ (certificate1543.bound:ℝ) :=
  rat_majority_certificate_sound certificate1543 valid1543 x hx0 hx1

def certificate1544 : RatMajorityCertificate := ⟨0,(200054548193195137/200000000000000000),(350130733/289402500),(2219691759618391193/5000000000000000000),(44393835192367823861/100000000000000000000),(364740092440520379/500000000000000000),false⟩
theorem valid1544 : certificate1544.Valid := by decide +kernel
theorem bound1544 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1544.a certificate1544.b certificate1544.c x ≤ (certificate1544.bound:ℝ) :=
  rat_majority_certificate_sound certificate1544 valid1544 x hx0 hx1

def certificate1545 : RatMajorityCertificate := ⟨(42421925388893067/250000000000000000),(41526937931138347823670309642584821/50000000000000000000000000000000000),(350130733/289402500),(408258302413111693883077/1000000000000000000000000),(204129151206555846941539/500000000000000000000000),(364740092440520379/500000000000000000),false⟩
theorem valid1545 : certificate1545.Valid := by decide +kernel
theorem bound1545 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1545.a certificate1545.b certificate1545.c x ≤ (certificate1545.bound:ℝ) :=
  rat_majority_certificate_sound certificate1545 valid1545 x hx0 hx1

def certificate1546 : RatMajorityCertificate := ⟨0,(200054548193195137/200000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(68497993615825201/125000000000000000),false⟩
theorem valid1546 : certificate1546.Valid := by decide +kernel
theorem bound1546 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1546.a certificate1546.b certificate1546.c x ≤ (certificate1546.bound:ℝ) :=
  rat_majority_certificate_sound certificate1546 valid1546 x hx0 hx1

def certificate1547 : RatMajorityCertificate := ⟨(19421293725840617/100000000000000000),(16120136677669133643942865558520471/20000000000000000000000000000000000),1,(34897403094192335527/100000000000000000000),(4362175386774041941/12500000000000000000),(68497993615825201/125000000000000000),false⟩
theorem valid1547 : certificate1547.Valid := by decide +kernel
theorem bound1547 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1547.a certificate1547.b certificate1547.c x ≤ (certificate1547.bound:ℝ) :=
  rat_majority_certificate_sound certificate1547 valid1547 x hx0 hx1

def certificate1548 : RatMajorityCertificate := ⟨0,(200056063375154177/200000000000000000),(73563181/60900000),(8870292548811532757/20000000000000000000),(22175731372028831893/50000000000000000000),(36376682326941129/50000000000000000),false⟩
theorem valid1548 : certificate1548.Valid := by decide +kernel
theorem bound1548 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1548.a certificate1548.b certificate1548.c x ≤ (certificate1548.bound:ℝ) :=
  rat_majority_certificate_sound certificate1548 valid1548 x hx0 hx1

def certificate1549 : RatMajorityCertificate := ⟨(83594185605026253/500000000000000000),(83304507994383555410539189992391219/100000000000000000000000000000000000),(73563181/60900000),(408428481948033952965893/1000000000000000000000000),(204214240974016976482947/500000000000000000000000),(36376682326941129/50000000000000000),false⟩
theorem valid1549 : certificate1549.Valid := by decide +kernel
theorem bound1549 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1549.a certificate1549.b certificate1549.c x ≤ (certificate1549.bound:ℝ) :=
  rat_majority_certificate_sound certificate1549 valid1549 x hx0 hx1

def certificate1550 : RatMajorityCertificate := ⟨0,(200056063375154177/200000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(27395125649864349/50000000000000000),false⟩
theorem valid1550 : certificate1550.Valid := by decide +kernel
theorem bound1550 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1550.a certificate1550.b certificate1550.c x ≤ (certificate1550.bound:ℝ) :=
  rat_majority_certificate_sound certificate1550 valid1550 x hx0 hx1

def certificate1551 : RatMajorityCertificate := ⟨(6048454884728279/31250000000000000),(5041721906732606595342555623128617/6250000000000000000000000000000000),1,(17457485006874704259/50000000000000000000),(34914970013749408519/100000000000000000000),(27395125649864349/50000000000000000),false⟩
theorem valid1551 : certificate1551.Valid := by decide +kernel
theorem bound1551 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1551.a certificate1551.b certificate1551.c x ≤ (certificate1551.bound:ℝ) :=
  rat_majority_certificate_sound certificate1551 valid1551 x hx0 hx1

def certificate1552 : RatMajorityCertificate := ⟨0,(1000282427088531617/1000000000000000000),(558545493/462850000),(44325162550600564429/100000000000000000000),(4432516255060056443/10000000000000000000),(726254236551053813/1000000000000000000),false⟩
theorem valid1552 : certificate1552.Valid := by decide +kernel
theorem bound1552 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1552.a certificate1552.b certificate1552.c x ≤ (certificate1552.bound:ℝ) :=
  rat_majority_certificate_sound certificate1552 valid1552 x hx0 hx1

def certificate1553 : RatMajorityCertificate := ⟨(164801796904340341/1000000000000000000),(835434085692506804306065548292938603/1000000000000000000000000000000000000),(558545493/462850000),(5109189164118802029/12500000000000000000),(40873513312950416233/100000000000000000000),(726254236551053813/1000000000000000000),false⟩
theorem valid1553 : certificate1553.Valid := by decide +kernel
theorem bound1553 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1553.a certificate1553.b certificate1553.c x ≤ (certificate1553.bound:ℝ) :=
  rat_majority_certificate_sound certificate1553 valid1553 x hx0 hx1

def certificate1554 : RatMajorityCertificate := ⟨0,(1000282427088531617/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(547748093443011979/1000000000000000000),false⟩
theorem valid1554 : certificate1554.Valid := by decide +kernel
theorem bound1554 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1554.a certificate1554.b certificate1554.c x ≤ (certificate1554.bound:ℝ) :=
  rat_majority_certificate_sound certificate1554 valid1554 x hx0 hx1

def certificate1555 : RatMajorityCertificate := ⟨(192332008960915039/1000000000000000000),(807896098358294309894112048797711937/1000000000000000000000000000000000000),1,(8736794811973728381/25000000000000000000),(1397887169915796541/4000000000000000000),(547748093443011979/1000000000000000000),false⟩
theorem valid1555 : certificate1555.Valid := by decide +kernel
theorem bound1555 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1555.a certificate1555.b certificate1555.c x ≤ (certificate1555.bound:ℝ) :=
  rat_majority_certificate_sound certificate1555 valid1555 x hx0 hx1

def certificate1556 : RatMajorityCertificate := ⟨0,(1000286164340885199/1000000000000000000),(2789931917/2313760000),(44303930620149683353/100000000000000000000),(22151965310074841677/50000000000000000000),(181319943311073437/250000000000000000),false⟩
theorem valid1556 : certificate1556.Valid := by decide +kernel
theorem bound1556 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1556.a certificate1556.b certificate1556.c x ≤ (certificate1556.bound:ℝ) :=
  rat_majority_certificate_sound certificate1556 valid1556 x hx0 hx1

def certificate1557 : RatMajorityCertificate := ⟨(163523430550716809/1000000000000000000),(836715939215445557510625544971390009/1000000000000000000000000000000000000),(2789931917/2313760000),(40882462586889994427/100000000000000000000),(10220615646722498607/25000000000000000000),(181319943311073437/250000000000000000),false⟩
theorem valid1557 : certificate1557.Valid := by decide +kernel
theorem bound1557 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1557.a certificate1557.b certificate1557.c x ≤ (certificate1557.bound:ℝ) :=
  rat_majority_certificate_sound certificate1557 valid1557 x hx0 hx1

def certificate1558 : RatMajorityCertificate := ⟨0,(1000286164340885199/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(10953644233276521/20000000000000000),false⟩
theorem valid1558 : certificate1558.Valid := by decide +kernel
theorem bound1558 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1558.a certificate1558.b certificate1558.c x ≤ (certificate1558.bound:ℝ) :=
  rat_majority_certificate_sound certificate1558 valid1558 x hx0 hx1

def certificate1559 : RatMajorityCertificate := ⟨(191801517478560543/1000000000000000000),(808429760107494622746591859065896943/1000000000000000000000000000000000000),1,(34961189274825850353/100000000000000000000),(17480594637412925177/50000000000000000000),(10953644233276521/20000000000000000),false⟩
theorem valid1559 : certificate1559.Valid := by decide +kernel
theorem bound1559 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1559.a certificate1559.b certificate1559.c x ≤ (certificate1559.bound:ℝ) :=
  rat_majority_certificate_sound certificate1559 valid1559 x hx0 hx1

end Cycle12.MajorityCertificates.Batch038
