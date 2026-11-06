import Cycle12.RationalMajorityCertificate

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MajorityCertificates.Batch042

def certificate1680 : RatMajorityCertificate := ⟨0,(250000366724161703/250000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(17446589352770067/31250000000000000),false⟩
theorem valid1680 : certificate1680.Valid := by decide +kernel
theorem bound1680 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1680.a certificate1680.b certificate1680.c x ≤ (certificate1680.bound:ℝ) :=
  rat_majority_certificate_sound certificate1680 valid1680 x hx0 hx1

def certificate1681 : RatMajorityCertificate := ⟨(134008828789860951/500000000000000000),(91497927020340214987390798590640447/125000000000000000000000000000000000),1,(16394652311197749827/50000000000000000000),(6557860924479099931/20000000000000000000),(17446589352770067/31250000000000000),false⟩
theorem valid1681 : certificate1681.Valid := by decide +kernel
theorem bound1681 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1681.a certificate1681.b certificate1681.c x ≤ (certificate1681.bound:ℝ) :=
  rat_majority_certificate_sound certificate1681 valid1681 x hx0 hx1

def certificate1682 : RatMajorityCertificate := ⟨0,(250000366724161703/250000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(552133806997158239/1000000000000000000),false⟩
theorem valid1682 : certificate1682.Valid := by decide +kernel
theorem bound1682 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1682.a certificate1682.b certificate1682.c x ≤ (certificate1682.bound:ℝ) :=
  rat_majority_certificate_sound certificate1682 valid1682 x hx0 hx1

def certificate1683 : RatMajorityCertificate := ⟨(226161461561330033/1000000000000000000),(193459918394956794145986126357673801/250000000000000000000000000000000000),1,(34022660453279416783/100000000000000000000),(2126416278329963549/6250000000000000000),(552133806997158239/1000000000000000000),false⟩
theorem valid1683 : certificate1683.Valid := by decide +kernel
theorem bound1683 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1683.a certificate1683.b certificate1683.c x ≤ (certificate1683.bound:ℝ) :=
  rat_majority_certificate_sound certificate1683 valid1683 x hx0 hx1

def certificate1684 : RatMajorityCertificate := ⟨0,(1000001901445170099/1000000000000000000),(679848839/587500000),(4319428955975755569/10000000000000000000),(43194289559757555691/100000000000000000000),(342318514221011127/500000000000000000),false⟩
theorem valid1684 : certificate1684.Valid := by decide +kernel
theorem bound1684 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1684.a certificate1684.b certificate1684.c x ≤ (certificate1684.bound:ℝ) :=
  rat_majority_certificate_sound certificate1684 valid1684 x hx0 hx1

def certificate1685 : RatMajorityCertificate := ⟨(198130434325633863/1000000000000000000),(801871090385378837906371011970537563/1000000000000000000000000000000000000),(679848839/587500000),(3886348304278910427/10000000000000000000),(38863483042789104271/100000000000000000000),(342318514221011127/500000000000000000),false⟩
theorem valid1685 : certificate1685.Valid := by decide +kernel
theorem bound1685 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1685.a certificate1685.b certificate1685.c x ≤ (certificate1685.bound:ℝ) :=
  rat_majority_certificate_sound certificate1685 valid1685 x hx0 hx1

def certificate1686 : RatMajorityCertificate := ⟨0,(1000001901445170099/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(17438891601940259/31250000000000000),false⟩
theorem valid1686 : certificate1686.Valid := by decide +kernel
theorem bound1686 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1686.a certificate1686.b certificate1686.c x ≤ (certificate1686.bound:ℝ) :=
  rat_majority_certificate_sound certificate1686 valid1686 x hx0 hx1

def certificate1687 : RatMajorityCertificate := ⟨(266428989904665753/1000000000000000000),(733572404940388317418073493175080453/1000000000000000000000000000000000000),1,(2052381901514455021/6250000000000000000),(32838110424231280337/100000000000000000000),(17438891601940259/31250000000000000),false⟩
theorem valid1687 : certificate1687.Valid := by decide +kernel
theorem bound1687 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1687.a certificate1687.b certificate1687.c x ≤ (certificate1687.bound:ℝ) :=
  rat_majority_certificate_sound certificate1687 valid1687 x hx0 hx1

def certificate1688 : RatMajorityCertificate := ⟨0,(1000001901445170099/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(110369104527465789/200000000000000000),false⟩
theorem valid1688 : certificate1688.Valid := by decide +kernel
theorem bound1688 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1688.a certificate1688.b certificate1688.c x ≤ (certificate1688.bound:ℝ) :=
  rat_majority_certificate_sound certificate1688 valid1688 x hx0 hx1

def certificate1689 : RatMajorityCertificate := ⟨(224082020261476531/1000000000000000000),(775919455104018435789193055808553431/1000000000000000000000000000000000000),1,(34081224542427231373/100000000000000000000),(17040612271213615687/50000000000000000000),(110369104527465789/200000000000000000),false⟩
theorem valid1689 : certificate1689.Valid := by decide +kernel
theorem bound1689 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1689.a certificate1689.b certificate1689.c x ≤ (certificate1689.bound:ℝ) :=
  rat_majority_certificate_sound certificate1689 valid1689 x hx0 hx1

def certificate1690 : RatMajorityCertificate := ⟨0,(1000002388172223313/1000000000000000000),(11565033/10000000),(10794563047827179671/25000000000000000000),(8635650438261743737/20000000000000000000),(34178356456913199/50000000000000000),false⟩
theorem valid1690 : certificate1690.Valid := by decide +kernel
theorem bound1690 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1690.a certificate1690.b certificate1690.c x ≤ (certificate1690.bound:ℝ) :=
  rat_majority_certificate_sound certificate1690 valid1690 x hx0 hx1

def certificate1691 : RatMajorityCertificate := ⟨(193719787284474151/1000000000000000000),(806282138251534063115940000251917737/1000000000000000000000000000000000000),(11565033/10000000),(38961362691577744917/100000000000000000000),(19480681345788872459/50000000000000000000),(34178356456913199/50000000000000000),false⟩
theorem valid1691 : certificate1691.Valid := by decide +kernel
theorem bound1691 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1691.a certificate1691.b certificate1691.c x ≤ (certificate1691.bound:ℝ) :=
  rat_majority_certificate_sound certificate1691 valid1691 x hx0 hx1

def certificate1692 : RatMajorityCertificate := ⟨0,(1000002388172223313/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(27515471268724391/50000000000000000),false⟩
theorem valid1692 : certificate1692.Valid := by decide +kernel
theorem bound1692 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1692.a certificate1692.b certificate1692.c x ≤ (certificate1692.bound:ℝ) :=
  rat_majority_certificate_sound certificate1692 valid1692 x hx0 hx1

def certificate1693 : RatMajorityCertificate := ⟨(212812758614700729/1000000000000000000),(787189121324003693757366097948104823/1000000000000000000000000000000000000),1,(34394394958874390451/100000000000000000000),(8598598739718597613/25000000000000000000),(27515471268724391/50000000000000000),false⟩
theorem valid1693 : certificate1693.Valid := by decide +kernel
theorem bound1693 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1693.a certificate1693.b certificate1693.c x ≤ (certificate1693.bound:ℝ) :=
  rat_majority_certificate_sound certificate1693 valid1693 x hx0 hx1

def certificate1694 : RatMajorityCertificate := ⟨0,(1000002388172223313/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(551559649661987641/1000000000000000000),false⟩
theorem valid1694 : certificate1694.Valid := by decide +kernel
theorem bound1694 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1694.a certificate1694.b certificate1694.c x ≤ (certificate1694.bound:ℝ) :=
  rat_majority_certificate_sound certificate1694 valid1694 x hx0 hx1

def certificate1695 : RatMajorityCertificate := ⟨(222008560396915777/1000000000000000000),(777993297580630258379207093903090799/1000000000000000000000000000000000000),1,(426742219280987989/1250000000000000000),(34139377542479039121/100000000000000000000),(551559649661987641/1000000000000000000),false⟩
theorem valid1695 : certificate1695.Valid := by decide +kernel
theorem bound1695 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1695.a certificate1695.b certificate1695.c x ≤ (certificate1695.bound:ℝ) :=
  rat_majority_certificate_sound certificate1695 valid1695 x hx0 hx1

def certificate1696 : RatMajorityCertificate := ⟨0,(200000585145005241/200000000000000000),(1358997793/1175000000),(43180369403922314157/100000000000000000000),(21590184701961157079/50000000000000000000),(341854647581501871/500000000000000000),false⟩
theorem valid1696 : certificate1696.Valid := by decide +kernel
theorem bound1696 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1696.a certificate1696.b certificate1696.c x ≤ (certificate1696.bound:ℝ) :=
  rat_majority_certificate_sound certificate1696 valid1696 x hx0 hx1

def certificate1697 : RatMajorityCertificate := ⟨(9715553318332393/50000000000000000),(8056912908576286075176956634928287/10000000000000000000000000000000000),(1358997793/1175000000),(38948265515931881129/100000000000000000000),(3894826551593188113/10000000000000000000),(341854647581501871/500000000000000000),false⟩
theorem valid1697 : certificate1697.Valid := by decide +kernel
theorem bound1697 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1697.a certificate1697.b certificate1697.c x ≤ (certificate1697.bound:ℝ) :=
  rat_majority_certificate_sound certificate1697 valid1697 x hx0 hx1

def certificate1698 : RatMajorityCertificate := ⟨0,(200000585145005241/200000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(555154270703377929/1000000000000000000),false⟩
theorem valid1698 : certificate1698.Valid := by decide +kernel
theorem bound1698 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1698.a certificate1698.b certificate1698.c x ≤ (certificate1698.bound:ℝ) :=
  rat_majority_certificate_sound certificate1698 valid1698 x hx0 hx1

def certificate1699 : RatMajorityCertificate := ⟨(247273735906581237/1000000000000000000),(150545693272697500581872189242736883/200000000000000000000000000000000000),1,(33413899890124519249/100000000000000000000),(133655599560498077/400000000000000000),(555154270703377929/1000000000000000000),false⟩
theorem valid1699 : certificate1699.Valid := by decide +kernel
theorem bound1699 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1699.a certificate1699.b certificate1699.c x ≤ (certificate1699.bound:ℝ) :=
  rat_majority_certificate_sound certificate1699 valid1699 x hx0 hx1

def certificate1700 : RatMajorityCertificate := ⟨0,(200000585145005241/200000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(551275364620053391/1000000000000000000),false⟩
theorem valid1700 : certificate1700.Valid := by decide +kernel
theorem bound1700 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1700.a certificate1700.b certificate1700.c x ≤ (certificate1700.bound:ℝ) :=
  rat_majority_certificate_sound certificate1700 valid1700 x hx0 hx1

def certificate1701 : RatMajorityCertificate := ⟨(109967621524710569/500000000000000000),(78006703920556033282929691486907871/100000000000000000000000000000000000),1,(34197285897907147913/100000000000000000000),(17098642948953573957/50000000000000000000),(551275364620053391/1000000000000000000),false⟩
theorem valid1701 : certificate1701.Valid := by decide +kernel
theorem bound1701 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1701.a certificate1701.b certificate1701.c x ≤ (certificate1701.bound:ℝ) :=
  rat_majority_certificate_sound certificate1701 valid1701 x hx0 hx1

def certificate1702 : RatMajorityCertificate := ⟨0,(62500219547024099/62500000000000000),(2720757753/2350000000),(10801957614962034617/25000000000000000000),(43207830459848138469/100000000000000000000),(68553524238397789/100000000000000000),false⟩
theorem valid1702 : certificate1702.Valid := by decide +kernel
theorem bound1702 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1702.a certificate1702.b certificate1702.c x ≤ (certificate1702.bound:ℝ) :=
  rat_majority_certificate_sound certificate1702 valid1702 x hx0 hx1

def certificate1703 : RatMajorityCertificate := ⟨(201752690725324007/1000000000000000000),(49890632082488495851696445587755307/62500000000000000000000000000000000),(2720757753/2350000000),(7756553541543486163/20000000000000000000),(1211961490866169713/3125000000000000000),(68553524238397789/100000000000000000),false⟩
theorem valid1703 : certificate1703.Valid := by decide +kernel
theorem bound1703 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1703.a certificate1703.b certificate1703.c x ≤ (certificate1703.bound:ℝ) :=
  rat_majority_certificate_sound certificate1703 valid1703 x hx0 hx1

def certificate1704 : RatMajorityCertificate := ⟨0,(62500219547024099/62500000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(278660303103874087/500000000000000000),false⟩
theorem valid1704 : certificate1704.Valid := by decide +kernel
theorem bound1704 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1704.a certificate1704.b certificate1704.c x ≤ (certificate1704.bound:ℝ) :=
  rat_majority_certificate_sound certificate1704 valid1704 x hx0 hx1

def certificate1705 : RatMajorityCertificate := ⟨(32714929683589501/125000000000000000),(5767837155688212922385379129615401/7812500000000000000000000000000000),1,(32981834891923371357/100000000000000000000),(16490917445961685679/50000000000000000000),(278660303103874087/500000000000000000),false⟩
theorem valid1705 : certificate1705.Valid := by decide +kernel
theorem bound1705 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1705.a certificate1705.b certificate1705.c x ≤ (certificate1705.bound:ℝ) :=
  rat_majority_certificate_sound certificate1705 valid1705 x hx0 hx1

def certificate1706 : RatMajorityCertificate := ⟨0,(62500219547024099/62500000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(550992584856582553/1000000000000000000),false⟩
theorem valid1706 : certificate1706.Valid := by decide +kernel
theorem bound1706 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1706.a certificate1706.b certificate1706.c x ≤ (certificate1706.bound:ℝ) :=
  rat_majority_certificate_sound certificate1706 valid1706 x hx0 hx1

def certificate1707 : RatMajorityCertificate := ⟨(54465385768044373/250000000000000000),(12220956318539889659330416867655073/15625000000000000000000000000000000),1,(107046768228324653/312500000000000000),(34254965833063888961/100000000000000000000),(550992584856582553/1000000000000000000),false⟩
theorem valid1707 : certificate1707.Valid := by decide +kernel
theorem bound1707 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1707.a certificate1707.b certificate1707.c x ≤ (certificate1707.bound:ℝ) :=
  rat_majority_certificate_sound certificate1707 valid1707 x hx0 hx1

def certificate1708 : RatMajorityCertificate := ⟨0,(1000004147904727867/1000000000000000000),(543316227/470000000),(8633259042653633467/20000000000000000000),(5395786901658520917/12500000000000000000),(170692573998172499/250000000000000000),false⟩
theorem valid1708 : certificate1708.Valid := by decide +kernel
theorem bound1708 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1708.a certificate1708.b certificate1708.c x ≤ (certificate1708.bound:ℝ) :=
  rat_majority_certificate_sound certificate1708 valid1708 x hx0 hx1

def certificate1709 : RatMajorityCertificate := ⟨(190395611538703573/1000000000000000000),(809607746623167027482710897454431209/1000000000000000000000000000000000000),(543316227/470000000),(1561385583019469929/4000000000000000000),(19517319787743374113/50000000000000000000),(170692573998172499/250000000000000000),false⟩
theorem valid1709 : certificate1709.Valid := by decide +kernel
theorem bound1709 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1709.a certificate1709.b certificate1709.c x ≤ (certificate1709.bound:ℝ) :=
  rat_majority_certificate_sound certificate1709 valid1709 x hx0 hx1

def certificate1710 : RatMajorityCertificate := ⟨0,(1000004147904727867/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(137663875584546849/250000000000000000),false⟩
theorem valid1710 : certificate1710.Valid := by decide +kernel
theorem bound1710 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1710.a certificate1710.b certificate1710.c x ≤ (certificate1710.bound:ℝ) :=
  rat_majority_certificate_sound certificate1710 valid1710 x hx0 hx1

def certificate1711 : RatMajorityCertificate := ⟨(215375071521535121/1000000000000000000),(784628183027915317131202298412083093/1000000000000000000000000000000000000),1,(1716190667506474957/5000000000000000000),(34323813350129499141/100000000000000000000),(137663875584546849/250000000000000000),false⟩
theorem valid1711 : certificate1711.Valid := by decide +kernel
theorem bound1711 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1711.a certificate1711.b certificate1711.c x ≤ (certificate1711.bound:ℝ) :=
  rat_majority_certificate_sound certificate1711 valid1711 x hx0 hx1

def certificate1712 : RatMajorityCertificate := ⟨0,(1000004147904727867/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(137677848875185631/250000000000000000),false⟩
theorem valid1712 : certificate1712.Valid := by decide +kernel
theorem bound1712 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1712.a certificate1712.b certificate1712.c x ≤ (certificate1712.bound:ℝ) :=
  rat_majority_certificate_sound certificate1712 valid1712 x hx0 hx1

def certificate1713 : RatMajorityCertificate := ⟨(26973520325393019/125000000000000000),(98026886279105479460676234983439527/125000000000000000000000000000000000),1,(1072262481014096051/3125000000000000000),(34312399392451073633/100000000000000000000),(137677848875185631/250000000000000000),false⟩
theorem valid1713 : certificate1713.Valid := by decide +kernel
theorem bound1713 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1713.a certificate1713.b certificate1713.c x ≤ (certificate1713.bound:ℝ) :=
  rat_majority_certificate_sound certificate1713 valid1713 x hx0 hx1

def certificate1714 : RatMajorityCertificate := ⟨0,(1000004829834124227/1000000000000000000),(2717605461/2350000000),(1727059534242170459/4000000000000000000),(10794122089013565369/25000000000000000000),(170862690123016829/250000000000000000),false⟩
theorem valid1714 : certificate1714.Valid := by decide +kernel
theorem bound1714 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1714.a certificate1714.b certificate1714.c x ≤ (certificate1714.bound:ℝ) :=
  rat_majority_certificate_sound certificate1714 valid1714 x hx0 hx1

def certificate1715 : RatMajorityCertificate := ⟨(38646298499989429/200000000000000000),(161354480811624146088332417027203617/200000000000000000000000000000000000),(2717605461/2350000000),(38972161444162050162181/100000000000000000000000),(389721614441620501621811/1000000000000000000000000),(170862690123016829/250000000000000000),false⟩
theorem valid1715 : certificate1715.Valid := by decide +kernel
theorem bound1715 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1715.a certificate1715.b certificate1715.c x ≤ (certificate1715.bound:ℝ) :=
  rat_majority_certificate_sound certificate1715 valid1715 x hx0 hx1

def certificate1716 : RatMajorityCertificate := ⟨0,(1000004829834124227/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(275924784763951061/500000000000000000),false⟩
theorem valid1716 : certificate1716.Valid := by decide +kernel
theorem bound1716 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1716.a certificate1716.b certificate1716.c x ≤ (certificate1716.bound:ℝ) :=
  rat_majority_certificate_sound certificate1716 valid1716 x hx0 hx1

def certificate1717 : RatMajorityCertificate := ⟨(224102718139302241/1000000000000000000),(775901029315866584772933850906507293/1000000000000000000000000000000000000),1,(6816131431342387509/20000000000000000000),(17040328578355968773/50000000000000000000),(275924784763951061/500000000000000000),false⟩
theorem valid1717 : certificate1717.Valid := by decide +kernel
theorem bound1717 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1717.a certificate1717.b certificate1717.c x ≤ (certificate1717.bound:ℝ) :=
  rat_majority_certificate_sound certificate1717 valid1717 x hx0 hx1

def certificate1718 : RatMajorityCertificate := ⟨0,(1000004829834124227/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(552360207694683039/1000000000000000000),false⟩
theorem valid1718 : certificate1718.Valid := by decide +kernel
theorem bound1718 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1718.a certificate1718.b certificate1718.c x ≤ (certificate1718.bound:ℝ) :=
  rat_majority_certificate_sound certificate1718 valid1718 x hx0 hx1

def certificate1719 : RatMajorityCertificate := ⟨(227775951569564757/1000000000000000000),(772227778144495901039635807340932161/1000000000000000000000000000000000000),1,(8494260027626883159/25000000000000000000),(33977040110507532637/100000000000000000000),(552360207694683039/1000000000000000000),false⟩
theorem valid1719 : certificate1719.Valid := by decide +kernel
theorem bound1719 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1719.a certificate1719.b certificate1719.c x ≤ (certificate1719.bound:ℝ) :=
  rat_majority_certificate_sound certificate1719 valid1719 x hx0 hx1

end Cycle12.MajorityCertificates.Batch042
