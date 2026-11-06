import Cycle12.RationalMajorityCertificate

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MajorityCertificates.Batch040

def certificate1600 : RatMajorityCertificate := ⟨0,(500166774032030507/500000000000000000),(1370829413/1154105000),(877974981232031673/2000000000000000000),(43898749061601583651/100000000000000000000),(707401170754404581/1000000000000000000),false⟩
theorem valid1600 : certificate1600.Valid := by decide +kernel
theorem bound1600 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1600.a certificate1600.b certificate1600.c x ≤ (certificate1600.bound:ℝ) :=
  rat_majority_certificate_sound certificate1600 valid1600 x hx0 hx1

def certificate1601 : RatMajorityCertificate := ⟨(145463038790670933/1000000000000000000),(427410995179204510263594001145846969/500000000000000000000000000000000000),(1370829413/1154105000),(40894148267007311093/100000000000000000000),(20447074133503655547/50000000000000000000),(707401170754404581/1000000000000000000),false⟩
theorem valid1601 : certificate1601.Valid := by decide +kernel
theorem bound1601 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1601.a certificate1601.b certificate1601.c x ≤ (certificate1601.bound:ℝ) :=
  rat_majority_certificate_sound certificate1601 valid1601 x hx0 hx1

def certificate1602 : RatMajorityCertificate := ⟨0,(500166774032030507/500000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(546660680353036237/1000000000000000000),false⟩
theorem valid1602 : certificate1602.Valid := by decide +kernel
theorem bound1602 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1602.a certificate1602.b certificate1602.c x ≤ (certificate1602.bound:ℝ) :=
  rat_majority_certificate_sound certificate1602 valid1602 x hx0 hx1

def certificate1603 : RatMajorityCertificate := ⟨(45879064190402609/250000000000000000),(102094509976285502358582493899607237/125000000000000000000000000000000000),1,(3517810083375905273/10000000000000000000),(35178100833759052731/100000000000000000000),(546660680353036237/1000000000000000000),false⟩
theorem valid1603 : certificate1603.Valid := by decide +kernel
theorem bound1603 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1603.a certificate1603.b certificate1603.c x ≤ (certificate1603.bound:ℝ) :=
  rat_majority_certificate_sound certificate1603 valid1603 x hx0 hx1

def certificate1604 : RatMajorityCertificate := ⟨0,(500168536670381579/500000000000000000),(912400611/769280000),(5482402554243150281/12500000000000000000),(43859220433945202249/100000000000000000000),(352849080541217031/500000000000000000),false⟩
theorem valid1604 : certificate1604.Valid := by decide +kernel
theorem bound1604 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1604.a certificate1604.b certificate1604.c x ≤ (certificate1604.bound:ℝ) :=
  rat_majority_certificate_sound certificate1604 valid1604 x hx0 hx1

def certificate1605 : RatMajorityCertificate := ⟨(71988365138957591/500000000000000000),(214077953086345260751960279731383811/250000000000000000000000000000000000),(912400611/769280000),(8177654083475609491/20000000000000000000),(1277758450543063983/3125000000000000000),(352849080541217031/500000000000000000),false⟩
theorem valid1605 : certificate1605.Valid := by decide +kernel
theorem bound1605 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1605.a certificate1605.b certificate1605.c x ≤ (certificate1605.bound:ℝ) :=
  rat_majority_certificate_sound certificate1605 valid1605 x hx0 hx1

def certificate1606 : RatMajorityCertificate := ⟨0,(500168536670381579/500000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(546577789594147311/1000000000000000000),false⟩
theorem valid1606 : certificate1606.Valid := by decide +kernel
theorem bound1606 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1606.a certificate1606.b certificate1606.c x ≤ (certificate1606.bound:ℝ) :=
  rat_majority_certificate_sound certificate1606 valid1606 x hx0 hx1

def certificate1607 : RatMajorityCertificate := ⟨(91418567152261983/500000000000000000),(204359577378140900976982190414788843/250000000000000000000000000000000000),1,(439946577499298799/1250000000000000000),(35195726199943903921/100000000000000000000),(546577789594147311/1000000000000000000),false⟩
theorem valid1607 : certificate1607.Valid := by decide +kernel
theorem bound1607 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1607.a certificate1607.b certificate1607.c x ≤ (certificate1607.bound:ℝ) :=
  rat_majority_certificate_sound certificate1607 valid1607 x hx0 hx1

def certificate1608 : RatMajorityCertificate := ⟨0,(500170288660025089/500000000000000000),(455467053/384580000),(10955015761412645471/25000000000000000000),(8764012609130116377/20000000000000000000),(88002791959582963/125000000000000000),false⟩
theorem valid1608 : certificate1608.Valid := by decide +kernel
theorem bound1608 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1608.a certificate1608.b certificate1608.c x ≤ (certificate1608.bound:ℝ) :=
  rat_majority_certificate_sound certificate1608 valid1608 x hx0 hx1

def certificate1609 : RatMajorityCertificate := ⟨(17825063150799149/125000000000000000),(53605719100984749446978259260150739/62500000000000000000000000000000000),(455467053/384580000),(40880141289556721691/100000000000000000000),(10220035322389180423/25000000000000000000),(88002791959582963/125000000000000000),false⟩
theorem valid1609 : certificate1609.Valid := by decide +kernel
theorem bound1609 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1609.a certificate1609.b certificate1609.c x ≤ (certificate1609.bound:ℝ) :=
  rat_majority_certificate_sound certificate1609 valid1609 x hx0 hx1

def certificate1610 : RatMajorityCertificate := ⟨0,(500170288660025089/500000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(5464489174036439/10000000000000000),false⟩
theorem valid1610 : certificate1610.Valid := by decide +kernel
theorem bound1610 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1610.a certificate1610.b certificate1610.c x ≤ (certificate1610.bound:ℝ) :=
  rat_majority_certificate_sound certificate1610 valid1610 x hx0 hx1

def certificate1611 : RatMajorityCertificate := ⟨(181785739461320789/1000000000000000000),(409246462879380156238593702182724779/500000000000000000000000000000000000),1,(17611480237381620971/50000000000000000000),(35222960474763241943/100000000000000000000),(5464489174036439/10000000000000000),false⟩
theorem valid1611 : certificate1611.Valid := by decide +kernel
theorem bound1611 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1611.a certificate1611.b certificate1611.c x ≤ (certificate1611.bound:ℝ) :=
  rat_majority_certificate_sound certificate1611 valid1611 x hx0 hx1

def certificate1612 : RatMajorityCertificate := ⟨0,(62521503701457681/62500000000000000),(389769277/329590000),(43780535101564534489/100000000000000000000),(4378053510156453449/10000000000000000000),(351161645065036967/500000000000000000),false⟩
theorem valid1612 : certificate1612.Valid := by decide +kernel
theorem bound1612 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1612.a certificate1612.b certificate1612.c x ≤ (certificate1612.bound:ℝ) :=
  rat_majority_certificate_sound certificate1612 valid1612 x hx0 hx1

def certificate1613 : RatMajorityCertificate := ⟨(70542613608456263/500000000000000000),(26850321572897243274009938766093897/31250000000000000000000000000000000),(389769277/329590000),(10218702916529769447/25000000000000000000),(40874811666119077789/100000000000000000000),(351161645065036967/500000000000000000),false⟩
theorem valid1613 : certificate1613.Valid := by decide +kernel
theorem bound1613 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1613.a certificate1613.b certificate1613.c x ≤ (certificate1613.bound:ℝ) :=
  rat_majority_certificate_sound certificate1613 valid1613 x hx0 hx1

def certificate1614 : RatMajorityCertificate := ⟨0,(62521503701457681/62500000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(546366955306748703/1000000000000000000),false⟩
theorem valid1614 : certificate1614.Valid := by decide +kernel
theorem bound1614 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1614.a certificate1614.b certificate1614.c x ≤ (certificate1614.bound:ℝ) :=
  rat_majority_certificate_sound certificate1614 valid1614 x hx0 hx1

def certificate1615 : RatMajorityCertificate := ⟨(90555609760202817/500000000000000000),(25599078959918562772393214897512623/31250000000000000000000000000000000),1,(8810102119226308891/25000000000000000000),(7048081695381047113/20000000000000000000),(546366955306748703/1000000000000000000),false⟩
theorem valid1615 : certificate1615.Valid := by decide +kernel
theorem bound1615 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1615.a certificate1615.b certificate1615.c x ≤ (certificate1615.bound:ℝ) :=
  rat_majority_certificate_sound certificate1615 valid1615 x hx0 hx1

def certificate1616 : RatMajorityCertificate := ⟨0,(1000353246341731947/1000000000000000000),(1360667577/1152925000),(43725727712794672699/100000000000000000000),(437257277127946727/1000000000000000000),(140007963710336297/200000000000000000),false⟩
theorem valid1616 : certificate1616.Valid := by decide +kernel
theorem bound1616 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1616.a certificate1616.b certificate1616.c x ≤ (certificate1616.bound:ℝ) :=
  rat_majority_certificate_sound certificate1616 valid1616 x hx0 hx1

def certificate1617 : RatMajorityCertificate := ⟨(139759096803253241/1000000000000000000),(860544780148809195744092508019009773/1000000000000000000000000000000000000),(1360667577/1152925000),(20424671862144676473/50000000000000000000),(40849343724289352947/100000000000000000000),(140007963710336297/200000000000000000),false⟩
theorem valid1617 : certificate1617.Valid := by decide +kernel
theorem bound1617 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1617.a certificate1617.b certificate1617.c x ≤ (certificate1617.bound:ℝ) :=
  rat_majority_certificate_sound certificate1617 valid1617 x hx0 hx1

def certificate1618 : RatMajorityCertificate := ⟨0,(1000353246341731947/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(546306892425773309/1000000000000000000),false⟩
theorem valid1618 : certificate1618.Valid := by decide +kernel
theorem bound1618 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1618.a certificate1618.b certificate1618.c x ≤ (certificate1618.bound:ℝ) :=
  rat_majority_certificate_sound certificate1618 valid1618 x hx0 hx1

def certificate1619 : RatMajorityCertificate := ⟨(90296550234430491/500000000000000000),(409848176010394154947780975874404023/500000000000000000000000000000000000),1,(35253820388854581121/100000000000000000000),(17626910194427290561/50000000000000000000),(546306892425773309/1000000000000000000),false⟩
theorem valid1619 : certificate1619.Valid := by decide +kernel
theorem bound1619 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1619.a certificate1619.b certificate1619.c x ≤ (certificate1619.bound:ℝ) :=
  rat_majority_certificate_sound certificate1619 valid1619 x hx0 hx1

def certificate1620 : RatMajorityCertificate := ⟨0,(1000354366301126869/1000000000000000000),(1356745859/1153065000),(43644584283530071633/100000000000000000000),(21822292141765035817/50000000000000000000),(174140614104088339/250000000000000000),false⟩
theorem valid1620 : certificate1620.Valid := by decide +kernel
theorem bound1620 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1620.a certificate1620.b certificate1620.c x ≤ (certificate1620.bound:ℝ) :=
  rat_majority_certificate_sound certificate1620 valid1620 x hx0 hx1

def certificate1621 : RatMajorityCertificate := ⟨(136590210988062031/1000000000000000000),(863715752345226859839438138227189061/1000000000000000000000000000000000000),(1356745859/1153065000),(5104926374849085919/12500000000000000000),(40839410998792687353/100000000000000000000),(174140614104088339/250000000000000000),false⟩
theorem valid1621 : certificate1621.Valid := by decide +kernel
theorem bound1621 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1621.a certificate1621.b certificate1621.c x ≤ (certificate1621.bound:ℝ) :=
  rat_majority_certificate_sound certificate1621 valid1621 x hx0 hx1

def certificate1622 : RatMajorityCertificate := ⟨0,(1000354366301126869/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(68256525790631719/125000000000000000),false⟩
theorem valid1622 : certificate1622.Valid := by decide +kernel
theorem bound1622 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1622.a certificate1622.b certificate1622.c x ≤ (certificate1622.bound:ℝ) :=
  rat_majority_certificate_sound certificate1622 valid1622 x hx0 hx1

def certificate1623 : RatMajorityCertificate := ⟨(178520640192083563/1000000000000000000),(821770464410103636683196260087445753/1000000000000000000000000000000000000),1,(35307199423816375931/100000000000000000000),(8826799855954093983/25000000000000000000),(68256525790631719/125000000000000000),false⟩
theorem valid1623 : certificate1623.Valid := by decide +kernel
theorem bound1623 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1623.a certificate1623.b certificate1623.c x ≤ (certificate1623.bound:ℝ) :=
  rat_majority_certificate_sound certificate1623 valid1623 x hx0 hx1

def certificate1624 : RatMajorityCertificate := ⟨0,(125044719222480411/125000000000000000),(2709205341/2305810000),(43605667490759652823/100000000000000000000),(5450708436344956603/12500000000000000000),(694912996304539663/1000000000000000000),false⟩
theorem valid1624 : certificate1624.Valid := by decide +kernel
theorem bound1624 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1624.a certificate1624.b certificate1624.c x ≤ (certificate1624.bound:ℝ) :=
  rat_majority_certificate_sound certificate1624 valid1624 x hx0 hx1

def certificate1625 : RatMajorityCertificate := ⟨(135213515073201723/1000000000000000000),(108136983195067278710908548581051847/125000000000000000000000000000000000),(2709205341/2305810000),(40831249853847362509/100000000000000000000),(4083124985384736251/10000000000000000000),(694912996304539663/1000000000000000000),false⟩
theorem valid1625 : certificate1625.Valid := by decide +kernel
theorem bound1625 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1625.a certificate1625.b certificate1625.c x ≤ (certificate1625.bound:ℝ) :=
  rat_majority_certificate_sound certificate1625 valid1625 x hx0 hx1

def certificate1626 : RatMajorityCertificate := ⟨0,(125044719222480411/125000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(545971592585996513/1000000000000000000),false⟩
theorem valid1626 : certificate1626.Valid := by decide +kernel
theorem bound1626 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1626.a certificate1626.b certificate1626.c x ≤ (certificate1626.bound:ℝ) :=
  rat_majority_certificate_sound certificate1626 valid1626 x hx0 hx1

def certificate1627 : RatMajorityCertificate := ⟨(177851710963278037/1000000000000000000),(102805301961839567792300093420966793/125000000000000000000000000000000000),1,(35324395107783175609/100000000000000000000),(3532439510778317561/10000000000000000000),(545971592585996513/1000000000000000000),false⟩
theorem valid1627 : certificate1627.Valid := by decide +kernel
theorem bound1627 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1627.a certificate1627.b certificate1627.c x ≤ (certificate1627.bound:ℝ) :=
  rat_majority_certificate_sound certificate1627 valid1627 x hx0 hx1

def certificate1628 : RatMajorityCertificate := ⟨0,(500180557697300367/500000000000000000),(450512157/384250000),(1360879078209069111/3125000000000000000),(43548130502690211553/100000000000000000000),(692506993331668381/1000000000000000000),false⟩
theorem valid1628 : certificate1628.Valid := by decide +kernel
theorem bound1628 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1628.a certificate1628.b certificate1628.c x ≤ (certificate1628.bound:ℝ) :=
  rat_majority_certificate_sound certificate1628 valid1628 x hx0 hx1

def certificate1629 : RatMajorityCertificate := ⟨(133517075849614873/1000000000000000000),(433397912236727245596672451248441609/500000000000000000000000000000000000),(450512157/384250000),(20405645861261175689/50000000000000000000),(40811291722522351379/100000000000000000000),(692506993331668381/1000000000000000000),false⟩
theorem valid1629 : certificate1629.Valid := by decide +kernel
theorem bound1629 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1629.a certificate1629.b certificate1629.c x ≤ (certificate1629.bound:ℝ) :=
  rat_majority_certificate_sound certificate1629 valid1629 x hx0 hx1

def certificate1630 : RatMajorityCertificate := ⟨0,(500180557697300367/500000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(272932121426157131/500000000000000000),false⟩
theorem valid1630 : certificate1630.Valid := by decide +kernel
theorem bound1630 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1630.a certificate1630.b certificate1630.c x ≤ (certificate1630.bound:ℝ) :=
  rat_majority_certificate_sound certificate1630 valid1630 x hx0 hx1

def certificate1631 : RatMajorityCertificate := ⟨(176963174774439639/1000000000000000000),(411667018246736312286399174505952487/500000000000000000000000000000000000),1,(17673598976932633903/50000000000000000000),(35347197953865267807/100000000000000000000),(272932121426157131/500000000000000000),false⟩
theorem valid1631 : certificate1631.Valid := by decide +kernel
theorem bound1631 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1631.a certificate1631.b certificate1631.c x ≤ (certificate1631.bound:ℝ) :=
  rat_majority_certificate_sound certificate1631 valid1631 x hx0 hx1

def certificate1632 : RatMajorityCertificate := ⟨0,(7815347268734153/7812500000000000),(39688943/33900000),(43509414250780465753/100000000000000000000),(21754707125390232877/50000000000000000000),(690875683994856141/1000000000000000000),false⟩
theorem valid1632 : certificate1632.Valid := by decide +kernel
theorem bound1632 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1632.a certificate1632.b certificate1632.c x ≤ (certificate1632.bound:ℝ) :=
  rat_majority_certificate_sound certificate1632 valid1632 x hx0 hx1

def certificate1633 : RatMajorityCertificate := ⟨(26434934356706383/200000000000000000),(1356471261722978745780009294801401/1562500000000000000000000000000000),(39688943/33900000),(40802432631205826781/100000000000000000000),(20401216315602913391/50000000000000000000),(690875683994856141/1000000000000000000),false⟩
theorem valid1633 : certificate1633.Valid := by decide +kernel
theorem bound1633 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1633.a certificate1633.b certificate1633.c x ≤ (certificate1633.bound:ℝ) :=
  rat_majority_certificate_sound certificate1633 valid1633 x hx0 hx1

def certificate1634 : RatMajorityCertificate := ⟨0,(7815347268734153/7812500000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(68217591992466883/125000000000000000),false⟩
theorem valid1634 : certificate1634.Valid := by decide +kernel
theorem bound1634 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1634.a certificate1634.b certificate1634.c x ≤ (certificate1634.bound:ℝ) :=
  rat_majority_certificate_sound certificate1634 valid1634 x hx0 hx1

def certificate1635 : RatMajorityCertificate := ⟨(87970131780373707/500000000000000000),(3220156505227149336821560825884829/3906250000000000000000000000000000),1,(35373399664741450379/100000000000000000000),(1768669983237072519/5000000000000000000),(68217591992466883/125000000000000000),false⟩
theorem valid1635 : certificate1635.Valid := by decide +kernel
theorem bound1635 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1635.a certificate1635.b certificate1635.c x ≤ (certificate1635.bound:ℝ) :=
  rat_majority_certificate_sound certificate1635 valid1635 x hx0 hx1

def certificate1636 : RatMajorityCertificate := ⟨0,(1000367758048426413/1000000000000000000),(168298026/144056875),(2715744502463394743/6250000000000000000),(43451912039414315889/100000000000000000000),(172119512286371603/250000000000000000),false⟩
theorem valid1636 : certificate1636.Valid := by decide +kernel
theorem bound1636 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1636.a certificate1636.b certificate1636.c x ≤ (certificate1636.bound:ℝ) :=
  rat_majority_certificate_sound certificate1636 valid1636 x hx0 hx1

def certificate1637 : RatMajorityCertificate := ⟨(32607809074353027/250000000000000000),(217472138653524931100236766606697849/250000000000000000000000000000000000),(168298026/144056875),(20391726033642800337/50000000000000000000),(1631338082691424027/4000000000000000000),(172119512286371603/250000000000000000),false⟩
theorem valid1637 : certificate1637.Valid := by decide +kernel
theorem bound1637 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1637.a certificate1637.b certificate1637.c x ≤ (certificate1637.bound:ℝ) :=
  rat_majority_certificate_sound certificate1637 valid1637 x hx0 hx1

def certificate1638 : RatMajorityCertificate := ⟨0,(1000367758048426413/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(272816691711521101/500000000000000000),false⟩
theorem valid1638 : certificate1638.Valid := by decide +kernel
theorem bound1638 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1638.a certificate1638.b certificate1638.c x ≤ (certificate1638.bound:ℝ) :=
  rat_majority_certificate_sound certificate1638 valid1638 x hx0 hx1

def certificate1639 : RatMajorityCertificate := ⟨(175047500138016851/1000000000000000000),(825255882783376882662608780972514537/1000000000000000000000000000000000000),1,(35396227567138593077/100000000000000000000),(17698113783569296539/50000000000000000000),(272816691711521101/500000000000000000),false⟩
theorem valid1639 : certificate1639.Valid := by decide +kernel
theorem bound1639 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1639.a certificate1639.b certificate1639.c x ≤ (certificate1639.bound:ℝ) :=
  rat_majority_certificate_sound certificate1639 valid1639 x hx0 hx1

end Cycle12.MajorityCertificates.Batch040
