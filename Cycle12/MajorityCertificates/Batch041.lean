import Cycle12.RationalMajorityCertificate

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MajorityCertificates.Batch041

def certificate1640 : RatMajorityCertificate := ⟨0,(8002968313767713/8000000000000000),(2686772999/2304620000),(21697552773474876077/50000000000000000000),(8679021109389950431/20000000000000000000),(686131379392823949/1000000000000000000),false⟩
theorem valid1640 : certificate1640.Valid := by decide +kernel
theorem bound1640 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1640.a certificate1640.b certificate1640.c x ≤ (certificate1640.bound:ℝ) :=
  rat_majority_certificate_sound certificate1640 valid1640 x hx0 hx1

def certificate1641 : RatMajorityCertificate := ⟨(128897241927133637/1000000000000000000),(6971407770892811359880950073137819/8000000000000000000000000000000000),(2686772999/2304620000),(5095040852034099461/12500000000000000000),(40760326816272795689/100000000000000000000),(686131379392823949/1000000000000000000),false⟩
theorem valid1641 : certificate1641.Valid := by decide +kernel
theorem bound1641 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1641.a certificate1641.b certificate1641.c x ≤ (certificate1641.bound:ℝ) :=
  rat_majority_certificate_sound certificate1641 valid1641 x hx0 hx1

def certificate1642 : RatMajorityCertificate := ⟨0,(8002968313767713/8000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(545525993874445773/1000000000000000000),false⟩
theorem valid1642 : certificate1642.Valid := by decide +kernel
theorem bound1642 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1642.a certificate1642.b certificate1642.c x ≤ (certificate1642.bound:ℝ) :=
  rat_majority_certificate_sound certificate1642 valid1642 x hx0 hx1

def certificate1643 : RatMajorityCertificate := ⟨(87076233426851617/500000000000000000),(3304615819886522049403359343558079/4000000000000000000000000000000000),1,(35419074595527262833/100000000000000000000),(17709537297763631417/50000000000000000000),(545525993874445773/1000000000000000000),false⟩
theorem valid1643 : certificate1643.Valid := by decide +kernel
theorem bound1643 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1643.a certificate1643.b certificate1643.c x ≤ (certificate1643.bound:ℝ) :=
  rat_majority_certificate_sound certificate1643 valid1643 x hx0 hx1

def certificate1644 : RatMajorityCertificate := ⟨0,(500187144989929619/500000000000000000),(53615853/46087000),(5417258564970700127/12500000000000000000),(43338068519765601017/100000000000000000000),(170943213506755231/250000000000000000),false⟩
theorem valid1644 : certificate1644.Valid := by decide +kernel
theorem bound1644 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1644.a certificate1644.b certificate1644.c x ≤ (certificate1644.bound:ℝ) :=
  rat_majority_certificate_sound certificate1644 valid1644 x hx0 hx1

def certificate1645 : RatMajorityCertificate := ⟨(7953292368697297/62500000000000000),(27283561958701705516210109254460157/31250000000000000000000000000000000),(53615853/46087000),(2546214271958101871/6250000000000000000),(40739428351329629937/100000000000000000000),(170943213506755231/250000000000000000),false⟩
theorem valid1645 : certificate1645.Valid := by decide +kernel
theorem bound1645 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1645.a certificate1645.b certificate1645.c x ≤ (certificate1645.bound:ℝ) :=
  rat_majority_certificate_sound certificate1645 valid1645 x hx0 hx1

def certificate1646 : RatMajorityCertificate := ⟨0,(500187144989929619/500000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(272688304585618911/500000000000000000),false⟩
theorem valid1646 : certificate1646.Valid := by decide +kernel
theorem bound1646 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1646.a certificate1646.b certificate1646.c x ≤ (certificate1646.bound:ℝ) :=
  rat_majority_certificate_sound certificate1646 valid1646 x hx0 hx1

def certificate1647 : RatMajorityCertificate := ⟨(86454345123738811/500000000000000000),(206850220435547850094716946971256991/250000000000000000000000000000000000),1,(35450754766211779373/100000000000000000000),(17725377383105889687/50000000000000000000),(272688304585618911/500000000000000000),false⟩
theorem valid1647 : certificate1647.Valid := by decide +kernel
theorem bound1647 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1647.a certificate1647.b certificate1647.c x ≤ (certificate1647.bound:ℝ) :=
  rat_majority_certificate_sound certificate1647 valid1647 x hx0 hx1

def certificate1648 : RatMajorityCertificate := ⟨0,(1000377512837367319/1000000000000000000),(2676688059/2304080000),(43299829205904282083/100000000000000000000),(10824957301476070521/25000000000000000000),(85272858580480353/125000000000000000),false⟩
theorem valid1648 : certificate1648.Valid := by decide +kernel
theorem bound1648 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1648.a certificate1648.b certificate1648.c x ≤ (certificate1648.bound:ℝ) :=
  rat_majority_certificate_sound certificate1648 valid1648 x hx0 hx1

def certificate1649 : RatMajorityCertificate := ⟨(125993972390752963/1000000000000000000),(874335976104605943196427114981383803/1000000000000000000000000000000000000),(2676688059/2304080000),(40728930980571865989/100000000000000000000),(4072893098057186599/10000000000000000000),(85272858580480353/125000000000000000),false⟩
theorem valid1649 : certificate1649.Valid := by decide +kernel
theorem bound1649 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1649.a certificate1649.b certificate1649.c x ≤ (certificate1649.bound:ℝ) :=
  rat_majority_certificate_sound certificate1649 valid1649 x hx0 hx1

def certificate1650 : RatMajorityCertificate := ⟨0,(1000377512837367319/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(272648244052371069/500000000000000000),false⟩
theorem valid1650 : certificate1650.Valid := by decide +kernel
theorem bound1650 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1650.a certificate1650.b certificate1650.c x ≤ (certificate1650.bound:ℝ) :=
  rat_majority_certificate_sound certificate1650 valid1650 x hx0 hx1

def certificate1651 : RatMajorityCertificate := ⟨(10764665691655389/62500000000000000),(51754865061191500978135078241167909/62500000000000000000000000000000000),1,(17733948679160018751/50000000000000000000),(35467897358320037503/100000000000000000000),(272648244052371069/500000000000000000),false⟩
theorem valid1651 : certificate1651.Valid := by decide +kernel
theorem bound1651 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1651.a certificate1651.b certificate1651.c x ≤ (certificate1651.bound:ℝ) :=
  rat_majority_certificate_sound certificate1651 valid1651 x hx0 hx1

def certificate1652 : RatMajorityCertificate := ⟨0,(200076141093329641/200000000000000000),(2670779983/2303820000),(43243157518768272367/100000000000000000000),(2702697344923017023/6250000000000000000),(169963661889119303/250000000000000000),false⟩
theorem valid1652 : certificate1652.Valid := by decide +kernel
theorem bound1652 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1652.a certificate1652.b certificate1652.c x ≤ (certificate1652.bound:ℝ) :=
  rat_majority_certificate_sound certificate1652 valid1652 x hx0 hx1

def certificate1653 : RatMajorityCertificate := ⟨(124417686441850143/1000000000000000000),(175183130506284385478593395778011337/200000000000000000000000000000000000),(2670779983/2303820000),(20353369245060770817/50000000000000000000),(8141347698024308327/20000000000000000000),(169963661889119303/250000000000000000),false⟩
theorem valid1653 : certificate1653.Valid := by decide +kernel
theorem bound1653 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1653.a certificate1653.b certificate1653.c x ≤ (certificate1653.bound:ℝ) :=
  rat_majority_certificate_sound certificate1653 valid1653 x hx0 hx1

def certificate1654 : RatMajorityCertificate := ⟨0,(200076141093329641/200000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(545147921424790823/1000000000000000000),false⟩
theorem valid1654 : certificate1654.Valid := by decide +kernel
theorem bound1654 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1654.a certificate1654.b certificate1654.c x ≤ (certificate1654.bound:ℝ) :=
  rat_majority_certificate_sound certificate1654 valid1654 x hx0 hx1

def certificate1655 : RatMajorityCertificate := ⟨(10686982834835769/62500000000000000),(10366548532808509260864186385271071/12500000000000000000000000000000000),1,(354994410711054661247013/1000000000000000000000000),(177497205355527330623507/500000000000000000000000),(545147921424790823/1000000000000000000),false⟩
theorem valid1655 : certificate1655.Valid := by decide +kernel
theorem bound1655 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1655.a certificate1655.b certificate1655.c x ≤ (certificate1655.bound:ℝ) :=
  rat_majority_certificate_sound certificate1655 valid1655 x hx0 hx1

def certificate1656 : RatMajorityCertificate := ⟨0,(1000383867158161091/1000000000000000000),(666228057/575892500),(172746531476216167/400000000000000000),(43186632869054041751/100000000000000000000),(169384968675581609/250000000000000000),false⟩
theorem valid1656 : certificate1656.Valid := by decide +kernel
theorem bound1656 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1656.a certificate1656.b certificate1656.c x ≤ (certificate1656.bound:ℝ) :=
  rat_majority_certificate_sound certificate1656 valid1656 x hx0 hx1

def certificate1657 : RatMajorityCertificate := ⟨(122860754713111963/1000000000000000000),(877475950236287878843589898926768367/1000000000000000000000000000000000000),(666228057/575892500),(20342099695101247343/50000000000000000000),(40684199390202494687/100000000000000000000),(169384968675581609/250000000000000000),false⟩
theorem valid1657 : certificate1657.Valid := by decide +kernel
theorem bound1657 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1657.a certificate1657.b certificate1657.c x ≤ (certificate1657.bound:ℝ) :=
  rat_majority_certificate_sound certificate1657 valid1657 x hx0 hx1

def certificate1658 : RatMajorityCertificate := ⟨0,(1000383867158161091/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(109007939969523513/200000000000000000),false⟩
theorem valid1658 : certificate1658.Valid := by decide +kernel
theorem bound1658 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1658.a certificate1658.b certificate1658.c x ≤ (certificate1658.bound:ℝ) :=
  rat_majority_certificate_sound certificate1658 valid1658 x hx0 hx1

def certificate1659 : RatMajorityCertificate := ⟨(85040402775948797/500000000000000000),(415118886585389270481018510706342473/500000000000000000000000000000000000),1,(7104502987359945111/20000000000000000000),(8880628734199931389/25000000000000000000),(109007939969523513/200000000000000000),false⟩
theorem valid1659 : certificate1659.Valid := by decide +kernel
theorem bound1659 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1659.a certificate1659.b certificate1659.c x ≤ (certificate1659.bound:ℝ) :=
  rat_majority_certificate_sound certificate1659 valid1659 x hx0 hx1

def certificate1660 : RatMajorityCertificate := ⟨0,(500000244936478539/500000000000000000),(1358871991/1175000000),(43177866463301495171/100000000000000000000),(10794466615825373793/25000000000000000000),(341770857457144327/500000000000000000),false⟩
theorem valid1660 : certificate1660.Valid := by decide +kernel
theorem bound1660 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1660.a certificate1660.b certificate1660.c x ≤ (certificate1660.bound:ℝ) :=
  rat_majority_certificate_sound certificate1660 valid1660 x hx0 hx1

def certificate1661 : RatMajorityCertificate := ⟨(38725197987909553/200000000000000000),(80637440508127305415865790142416933/100000000000000000000000000000000000),(1358871991/1175000000),(19481689896810478727/50000000000000000000),(7792675958724191491/20000000000000000000),(341770857457144327/500000000000000000),false⟩
theorem valid1661 : certificate1661.Valid := by decide +kernel
theorem bound1661 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1661.a certificate1661.b certificate1661.c x ≤ (certificate1661.bound:ℝ) :=
  rat_majority_certificate_sound certificate1661 valid1661 x hx0 hx1

def certificate1662 : RatMajorityCertificate := ⟨0,(500000244936478539/500000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(279109595106483531/500000000000000000),false⟩
theorem valid1662 : certificate1662.Valid := by decide +kernel
theorem bound1662 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1662.a certificate1662.b certificate1662.c x ≤ (certificate1662.bound:ℝ) :=
  rat_majority_certificate_sound certificate1662 valid1662 x hx0 hx1

def certificate1663 : RatMajorityCertificate := ⟨(133779413815567209/500000000000000000),(183110382792997144003322208659372349/250000000000000000000000000000000000),1,(32803410695096822059/100000000000000000000),(1640170534754841103/5000000000000000000),(279109595106483531/500000000000000000),false⟩
theorem valid1663 : certificate1663.Valid := by decide +kernel
theorem bound1663 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1663.a certificate1663.b certificate1663.c x ≤ (certificate1663.bound:ℝ) :=
  rat_majority_certificate_sound certificate1663 valid1663 x hx0 hx1

def certificate1664 : RatMajorityCertificate := ⟨0,(500000244936478539/500000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(550964254222862693/1000000000000000000),false⟩
theorem valid1664 : certificate1664.Valid := by decide +kernel
theorem bound1664 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1664.a certificate1664.b certificate1664.c x ≤ (certificate1664.bound:ℝ) :=
  rat_majority_certificate_sound certificate1664 valid1664 x hx0 hx1

def certificate1665 : RatMajorityCertificate := ⟨(217662406431639107/1000000000000000000),(391168988407195643809732297701375327/500000000000000000000000000000000000),1,(34260477729653101513/100000000000000000000),(17130238864826550757/50000000000000000000),(550964254222862693/1000000000000000000),false⟩
theorem valid1665 : certificate1665.Valid := by decide +kernel
theorem bound1665 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1665.a certificate1665.b certificate1665.c x ≤ (certificate1665.bound:ℝ) :=
  rat_majority_certificate_sound certificate1665 valid1665 x hx0 hx1

def certificate1666 : RatMajorityCertificate := ⟨0,(1000000759753995363/1000000000000000000),(2724323161/2350000000),(34594585360690239/80000000000000000),(43243231700862798751/100000000000000000000),(137575640479015793/200000000000000000),false⟩
theorem valid1666 : certificate1666.Valid := by decide +kernel
theorem bound1666 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1666.a certificate1666.b certificate1666.c x ≤ (certificate1666.bound:ℝ) :=
  rat_majority_certificate_sound certificate1666 valid1666 x hx0 hx1

def certificate1667 : RatMajorityCertificate := ⟨(8441303712075763/40000000000000000),(31558720264769830197916070593313031/40000000000000000000000000000000000),(2724323161/2350000000),(2410853715691094201/6250000000000000000),(38573659451057507217/100000000000000000000),(137575640479015793/200000000000000000),false⟩
theorem valid1667 : certificate1667.Valid := by decide +kernel
theorem bound1667 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1667.a certificate1667.b certificate1667.c x ≤ (certificate1667.bound:ℝ) :=
  rat_majority_certificate_sound certificate1667 valid1667 x hx0 hx1

def certificate1668 : RatMajorityCertificate := ⟨0,(1000000759753995363/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(139555644721170947/250000000000000000),false⟩
theorem valid1668 : certificate1668.Valid := by decide +kernel
theorem bound1668 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1668.a certificate1668.b certificate1668.c x ≤ (certificate1668.bound:ℝ) :=
  rat_majority_certificate_sound certificate1668 valid1668 x hx0 hx1

def certificate1669 : RatMajorityCertificate := ⟨(267579989841205079/1000000000000000000),(732420566617823922953489303101951323/1000000000000000000000000000000000000),1,(32802761749407886577/100000000000000000000),(16401380874703943289/50000000000000000000),(139555644721170947/250000000000000000),false⟩
theorem valid1669 : certificate1669.Valid := by decide +kernel
theorem bound1669 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1669.a certificate1669.b certificate1669.c x ≤ (certificate1669.bound:ℝ) :=
  rat_majority_certificate_sound certificate1669 valid1669 x hx0 hx1

def certificate1670 : RatMajorityCertificate := ⟨0,(1000000759753995363/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(27540366045816357/50000000000000000),false⟩
theorem valid1670 : certificate1670.Valid := by decide +kernel
theorem bound1670 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1670.a certificate1670.b certificate1670.c x ≤ (certificate1670.bound:ℝ) :=
  rat_majority_certificate_sound certificate1670 valid1670 x hx0 hx1

def certificate1671 : RatMajorityCertificate := ⟨(43301258598356199/200000000000000000),(156698860454138649252420505531694763/200000000000000000000000000000000000),1,(342925187932741176701557/1000000000000000000000000),(171462593966370588350779/500000000000000000000000),(27540366045816357/50000000000000000),false⟩
theorem valid1671 : certificate1671.Valid := by decide +kernel
theorem bound1671 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1671.a certificate1671.b certificate1671.c x ≤ (certificate1671.bound:ℝ) :=
  rat_majority_certificate_sound certificate1671 valid1671 x hx0 hx1

def certificate1672 : RatMajorityCertificate := ⟨0,(1000001085880980321/1000000000000000000),(543617967/470000000),(10795326730291987527/25000000000000000000),(43181306921167950109/100000000000000000000),(683771626459146931/1000000000000000000),false⟩
theorem valid1672 : certificate1672.Valid := by decide +kernel
theorem bound1672 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1672.a certificate1672.b certificate1672.c x ≤ (certificate1672.bound:ℝ) :=
  rat_majority_certificate_sound certificate1672 valid1672 x hx0 hx1

def certificate1673 : RatMajorityCertificate := ⟨(194577297693151639/1000000000000000000),(805423576900041914749446394572103881/1000000000000000000000000000000000000),(543617967/470000000),(194711689579852777641867/500000000000000000000000),(77884675831941111056747/200000000000000000000000),(683771626459146931/1000000000000000000),false⟩
theorem valid1673 : certificate1673.Valid := by decide +kernel
theorem bound1673 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1673.a certificate1673.b certificate1673.c x ≤ (certificate1673.bound:ℝ) :=
  rat_majority_certificate_sound certificate1673 valid1673 x hx0 hx1

def certificate1674 : RatMajorityCertificate := ⟨0,(1000001085880980321/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(139457742685636083/250000000000000000),false⟩
theorem valid1674 : certificate1674.Valid := by decide +kernel
theorem bound1674 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1674.a certificate1674.b certificate1674.c x ≤ (certificate1674.bound:ℝ) :=
  rat_majority_certificate_sound certificate1674 valid1674 x hx0 hx1

def certificate1675 : RatMajorityCertificate := ⟨(26504904794505323/100000000000000000),(73495175012420707527786806507251317/100000000000000000000000000000000000),1,(16440181820175705031/50000000000000000000),(32880363640351410063/100000000000000000000),(139457742685636083/250000000000000000),false⟩
theorem valid1675 : certificate1675.Valid := by decide +kernel
theorem bound1675 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1675.a certificate1675.b certificate1675.c x ≤ (certificate1675.bound:ℝ) :=
  rat_majority_certificate_sound certificate1675 valid1675 x hx0 hx1

def certificate1676 : RatMajorityCertificate := ⟨0,(1000001085880980321/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(137605523328880797/250000000000000000),false⟩
theorem valid1676 : certificate1676.Valid := by decide +kernel
theorem bound1676 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1676.a certificate1676.b certificate1676.c x ≤ (certificate1676.bound:ℝ) :=
  rat_majority_certificate_sound certificate1676 valid1676 x hx0 hx1

def certificate1677 : RatMajorityCertificate := ⟨(106827261958918637/500000000000000000),(393173164979879582541159625362857523/500000000000000000000000000000000000),1,(859280961353629417/2500000000000000000),(34371238454145176681/100000000000000000000),(137605523328880797/250000000000000000),false⟩
theorem valid1677 : certificate1677.Valid := by decide +kernel
theorem bound1677 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1677.a certificate1677.b certificate1677.c x ≤ (certificate1677.bound:ℝ) :=
  rat_majority_certificate_sound certificate1677 valid1677 x hx0 hx1

def certificate1678 : RatMajorityCertificate := ⟨0,(250000366724161703/250000000000000000),(2724926479/2350000000),(43249217025749182953/100000000000000000000),(21624608512874591477/50000000000000000000),(137657358609302933/200000000000000000),false⟩
theorem valid1678 : certificate1678.Valid := by decide +kernel
theorem bound1678 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1678.a certificate1678.b certificate1678.c x ≤ (certificate1678.bound:ℝ) :=
  rat_majority_certificate_sound certificate1678 valid1678 x hx0 hx1

def certificate1679 : RatMajorityCertificate := ⟨(53171457913677083/250000000000000000),(49207207703362825080426398582647651/62500000000000000000000000000000000),(2724926479/2350000000),(3853561230803648541/10000000000000000000),(38535612308036485411/100000000000000000000),(137657358609302933/200000000000000000),false⟩
theorem valid1679 : certificate1679.Valid := by decide +kernel
theorem bound1679 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1679.a certificate1679.b certificate1679.c x ≤ (certificate1679.bound:ℝ) :=
  rat_majority_certificate_sound certificate1679 valid1679 x hx0 hx1

end Cycle12.MajorityCertificates.Batch041
